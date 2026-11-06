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

def RetBoSlicesKept : ∀ {F : Type}, PanSemStateFiniteExact 64 F →
    Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop :=
  fun s r post _ _ => ∀ v, r = some (.returned v) →
    ∀ off ∈ ([24, 32] : List Nat), ∀ i, i < memW s (globN s "bo" + 80) →
      memW post (memW post (globN post "bo" + off) + 16 * i + 8) =
        memW s (memW s (globN s "bo" + off) + 16 * i + 8)

theorem blockSliceLengths_of_retBoSlicesKept {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat} {v : ValueHOL 64} {count : Nat}
    (h : BlockSliceLengths s count)
    (hcnt : count ≤ memW s (globN s "bo" + 80))
    (hq : RetBoSlicesKept s r post S Nd) (hr : r = some (.returned v)) :
    BlockSliceLengths post count := by
  have hkeep := hq v hr
  constructor
  · intro i hi
    rw [hkeep 24 (by simp) i (Nat.lt_of_lt_of_le hi hcnt)]
    exact h.1 i hi
  · intro i hi
    rw [hkeep 32 (by simp) i (Nat.lt_of_lt_of_le hi hcnt)]
    exact h.2 i hi

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
    ExecBlock.RetBoSlicesKept (ofString "build_block_access_list_rlp")) →
  (WorldKeeps WorldOK (fun s => [(locN s "out", 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40), (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    ExecBlock.RetBoSlicesKept (ofString "build_mpt_indexed")) →
  (WorldKeeps WorldOK (fun s => [(locN s "out", 32), (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    ExecBlock.RetBoSlicesKept (ofString "compute_state_root")) →
  (WorldKeeps (fun s => WorldOK s ∧ ExecBlock.DecodeTxReady s) (fun _ => [])
    ["heap_ptr", "scratch_ptr"]
    [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
    (fun s r post S Nd => RetDecodedTx s r post S Nd ∧ ExecBlock.RetBoSlicesKept s r post S Nd)
    (ofString "decode_transaction")) →
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
    ExecBlock.RetBoSlicesKept (ofString "process_general_purpose_requests")) →
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
    ExecBlock.RetBoSlicesKept (ofString "process_withdrawals")) →
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

namespace ExecBlock

private def progIteEqZeroRaise ( code : BitVec 64 ) ( cont : ProgHOL 64 ) : ProgHOL 64 :=
  .seq
    (.ite (.cmp .equal (.var .local (ofString "eq")) (.const 0#64))
      (.raise (ofString "BlockErr") (.const code))
      .skip)
    cont

private def progMemEqCheck ( src : MlS ) ( hdrOff len code : BitVec 64 ) ( cont : ProgHOL 64 ) :
    ProgHOL 64 :=
  .seq
    (.call (some (some (.local, ofString "eq"), none)) (ofString "memeq")
      [ .var .local src
      , .load .one (.op .add [.var .local (ofString "hdr"), .const hdrOff])
      , .const len ])
    (progIteEqZeroRaise code cont)

private def progExecBlockGuestTail : ProgHOL 64 :=
  .decCall (ofString "rqh") .one (ofString "alloc") [.const 32#64]
    (.seq
      (.call (some (none, none)) (ofString "compute_requests_hash")
        [ .load .one (.op .add [.var .global (ofString "bo"), .const 56#64])
        , .load .one (.op .add [.var .global (ofString "bo"), .const 64#64])
        , .var .local (ofString "rqh") ])
      (.decCall (ofString "balh") .one (ofString "alloc") [.const 32#64]
        (.seq
          (.call (some (none, none)) (ofString "keccak256")
            [ .rfield 0 (.var .local (ofString "bal"))
            , .rfield 1 (.var .local (ofString "bal"))
            , .var .local (ofString "balh") ])
          (.decCall (ofString "bgu") .one (ofString "max")
            [ .load .one (.op .add [.var .global (ofString "bo"), .const 0#64])
            , .load .one (.op .add [.var .global (ofString "bo"), .const 8#64]) ]
            (.seq
              (.ite
                (.cmp .notEqual (.var .local (ofString "bgu"))
                  (.load .one (.op .add [.var .local (ofString "hdr"), .const 112#64])))
                (.raise (ofString "BlockErr") (.const 110#64))
                .skip)
              (.decCall (ofString "eq") .one (ofString "memeq")
                [ .var .local (ofString "txroot")
                , .load .one (.op .add [.var .local (ofString "hdr"), .const 40#64])
                , .const 32#64 ]
                (progIteEqZeroRaise 111#64
                  (progMemEqCheck (ofString "root") 32#64 32#64 112#64
                    (progMemEqCheck (ofString "rroot") 48#64 32#64 113#64
                      (progMemEqCheck (ofString "bloom") 56#64 256#64 114#64
                        (progMemEqCheck (ofString "wroot") 192#64 32#64 115#64
                          (.seq
                            (.ite
                              (.cmp .notEqual
                                (.load .one (.op .add [.var .global (ofString "bo"), .const 48#64]))
                                (.load .one (.op .add [.var .local (ofString "hdr"), .const 200#64])))
                              (.raise (ofString "BlockErr") (.const 116#64))
                              .skip)
                            (progMemEqCheck (ofString "rqh") 224#64 32#64 117#64
                              (progMemEqCheck (ofString "balh") 232#64 32#64 118#64
                                (.return (.const 0#64))))))))))))))))

private def kExecBlockGuestTail : Nat :=
  (K.«alloc» + 1) + (K.«compute_requests_hash» + 1) + (K.«alloc» + 1) +
    (K.«keccak256» + 1) + (K.«max» + 1) + (K.«memeq» + 1) + (K.«memeq» + 1) +
    (K.«memeq» + 1) + (K.«memeq» + 1) + (K.«memeq» + 1) + (K.«memeq» + 1) +
    (K.«memeq» + 1)

private theorem terminating_progIteEqZeroRaise {Bc : Nat} (code : BitVec 64) {cont : ProgHOL 64}
    (hcont : TerminatingProgBoundedOn GuestInv cont Bc) :
    TerminatingProgBoundedOn GuestInv (progIteEqZeroRaise code cont) (0 + Bc) :=
  TerminatingProgBoundedOn.seq_guestInv (straight_guestInv _ rfl) hcont

private theorem terminating_progMemEqCheck {Bc : Nat}
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (src : MlS) (hdrOff len code : BitVec 64) {cont : ProgHOL 64}
    (hcont : TerminatingProgBoundedOn GuestInv cont Bc) :
    TerminatingProgBoundedOn GuestInv (progMemEqCheck src hdrOff len code cont)
      ((K.«memeq» + 1) + (0 + Bc)) :=
  TerminatingProgBoundedOn.seq_guestInv
    (TerminatingProgBoundedOn.call_guestInv hmeq _ _)
    (terminating_progIteEqZeroRaise code hcont)

private theorem terminating_progExecBlockGuestTail
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hcrh : TerminatingFunBoundedOn GuestInv (ofString "compute_requests_hash") K.«compute_requests_hash»)
    (hkec : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hmax : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max»)
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq») :
    TerminatingProgBoundedOn GuestInv progExecBlockGuestTail kExecBlockGuestTail := by
  unfold progExecBlockGuestTail
  refine TerminatingProgBoundedOn.mono_bound
    (TerminatingProgBoundedOn.decCall_guestInv hal _ _ _
      (TerminatingProgBoundedOn.seq_guestInv
        (TerminatingProgBoundedOn.call_guestInv hcrh _ _)
        (TerminatingProgBoundedOn.decCall_guestInv hal _ _ _
          (TerminatingProgBoundedOn.seq_guestInv
            (TerminatingProgBoundedOn.call_guestInv hkec _ _)
            (TerminatingProgBoundedOn.decCall_guestInv hmax _ _ _
              (TerminatingProgBoundedOn.seq_guestInv
                (straight_guestInv _ rfl)
                (TerminatingProgBoundedOn.decCall_guestInv hmeq _ _ _
                  (terminating_progIteEqZeroRaise _
                    (terminating_progMemEqCheck hmeq _ _ _ _
                      (terminating_progMemEqCheck hmeq _ _ _ _
                        (terminating_progMemEqCheck hmeq _ _ _ _
                          (terminating_progMemEqCheck hmeq _ _ _ _
                            (TerminatingProgBoundedOn.seq_guestInv
                              (straight_guestInv _ rfl)
                              (terminating_progMemEqCheck hmeq _ _ _ _
                                (terminating_progMemEqCheck hmeq _ _ _ _
                                  (straight_guestInv _ rfl)))))))))))))))) ?_
  unfold kExecBlockGuestTail
  omega

private theorem lookup_logs_bloom_fn :
    originalRuntimeCode.lookup (ofString "logs_bloom") =
      some ((sourceFunctionEntry Guest.Software.guestFn_logs_bloom).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 832 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_logs_bloom) rfl

private theorem lookup_compute_state_root_fn :
    originalRuntimeCode.lookup (ofString "compute_state_root") =
      some ((sourceFunctionEntry Guest.Software.guestFn_compute_state_root).2) :=
  originalRuntimeCode_lookup_of_guestAst_getElem 843 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_compute_state_root) rfl

private theorem bo_mem_worldTypedIvls {F : Type} {s : PanSemStateFiniteExact 64 F}
    (S Nd : List Nat) (hbo_nz : globN s "bo" ≠ 0) :
    (globN s "bo", 88) ∈ worldTypedIvls s S Nd := by
  unfold worldTypedIvls
  apply List.mem_append.2; left; apply List.mem_append.2; left; apply List.mem_append.2; left
  apply List.mem_append.2; left; apply List.mem_append.2; right
  have hr_in : ("bo", 88) ∈ typedRecords := by decide
  have hm : (globN s "bo", if globN s "bo" = 0 then 0 else 88) ∈
      typedRecords.map (fun r => (globN s r.1, if globN s r.1 = 0 then 0 else r.2)) :=
    List.mem_map.2 ⟨("bo", 88), hr_in, rfl⟩
  rwa [if_neg hbo_nz] at hm

private theorem bo_slot_eq_of_worldStep
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)} {S Nd : List Nat}
    {boKeep : List Nat} {off : Nat}
    (hA : ArenaOK s) (hW : WorldTypedWith s S Nd) (hbo_nz : globN s "bo" ≠ 0)
    (hstep : WorldStep R gw keep Q s r post)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hkeep : ("bo", boKeep) ∈ keep) (hoff : off ∈ boKeep) (hoff8 : off % 8 = 0) (hoff_lt : off + 8 ≤ 88)
    (hRzero : ∀ j ∈ R s, j.2 = 0 → j.1 % 8 = 0)
    (hRtyped : IvlsDisj (R s) (worldTypedIvls s S Nd)) :
    globN post "bo" = globN s "bo" ∧
      memW post (globN post "bo" + off) = memW s (globN s "bo" + off) := by
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (hstep.2.2.1 _ hbo_gw)
  have hbo8 : globN s "bo" % 8 = 0 := (bo_allocated_wordsOK hA hW hbo_nz).2.2.1
  refine ⟨hbo_eq, ?_⟩
  rw [hbo_eq]
  apply hstep.2.2.2.1 ("bo", boKeep) hkeep hbo_nz off hoff
  intro i hi
  dsimp only
  have hd : Disj i (globN s "bo", 88) := hRtyped i hi _ (bo_mem_worldTypedIvls S Nd hbo_nz)
  exact not_cellHits_of_disj hbo8 (by omega) (by omega) (hRzero i hi) ⟨by omega, by omega⟩ hd.flip

private theorem bo_array_in_worldOwned {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {off : Nat}
    (hbo_nz : globN s "bo" ≠ 0) (hoff : off ∈ ([24, 32] : List Nat))
    (hp_nz : memW s (globN s "bo" + off) ≠ 0) :
    (memW s (globN s "bo" + off), 16 * memW s (globN s "bo" + 80) + 16) ∈ worldOwned s S Nd := by
  apply blockOutObj_mem_worldOwned
  have h16_nz : 16 * memW s (globN s "bo" + 80) + 16 ≠ 0 := by omega
  unfold blockOutObjects
  rcases List.mem_cons.1 hoff with rfl | hoff'
  · simp [hbo_nz, hp_nz, h16_nz]
  · have := List.mem_singleton.1 hoff'
    subst this
    simp [hbo_nz, hp_nz, h16_nz]

private theorem bo_array_sub_allocated_wordsOK {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} {off : Nat}
    (hA : ArenaReady s) (hW : WorldTypedWith s S Nd)
    (hbo_nz : globN s "bo" ≠ 0) (hoff : off ∈ ([24, 32] : List Nat))
    (hp_nz : memW s (globN s "bo" + off) ≠ 0)
    (hin_full : Inside (memW s (globN s "bo" + off), 16 * memW s (globN s "bo" + 80) + 16)
      sourceBase (globN s "heap_ptr")) :
    let p := memW s (globN s "bo" + off)
    let ntx := memW s (globN s "bo" + 80)
    Inside (p, 16 * ntx) sourceBase (globN s "heap_ptr") ∧
      WordsOK s (p, 16 * ntx) ∧
      p % 8 = 0 ∧
      p + 16 * ntx ≤ 2 ^ 64 ∧
      IvlsDisj [(p, 16 * ntx)]
        ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
          ("keccak_pad", 136), ("keccak_st", 200)].map (bufferRegion s)) := by
  intro p ntx
  have h16_nz : 16 * ntx + 16 ≠ 0 := by omega
  have hbo_mem : (p, 16 * ntx + 16) ∈ blockOutObjects s := by
    unfold blockOutObjects
    rcases List.mem_cons.1 hoff with rfl | hoff'
    · simp [p, ntx, hbo_nz, hp_nz, h16_nz]
    · have := List.mem_singleton.1 hoff'
      subst this
      simp [p, ntx, hbo_nz, hp_nz, h16_nz]
  have hfix : (p, 16 * ntx + 16) ∈ fixedObjects s := by
    unfold fixedObjects
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hbo_mem)))
  rcases hW.2.2.1.1 _ hfix with hz | ⟨hal, hw_full⟩
  · dsimp only at hz; omega
  · have hp8 : p % 8 = 0 := hw_full.1
    have hbound_full : p + (16 * ntx + 16) ≤ 2 ^ 64 := (ivl_allocated_bound hA.2 hal).2
    have hin_sub : Inside (p, 16 * ntx) sourceBase (globN s "heap_ptr") :=
      ⟨hin_full.1, by have := hin_full.2; dsimp only at this ⊢; omega⟩
    have hw_sub : WordsOK s (p, 16 * ntx) :=
      wordsOK_of_inside_heap hA.1 hp8 (by omega) hin_sub.1
        (hin_sub.2.trans (hA.2.2.1.trans (by decide)))
    let f_s : String × Nat → Ivl := fun gn => (globN s gn.1, if globN s gn.1 = 0 then 0 else gn.2)
    let jr_s : List Ivl := [(if globN s "journal_cap" = 0 then 0 else globN s "journal",
      32 * globN s "journal_cap")]
    have hF_parts := (pairwise_disj_append_4 (a1 := globalBuffers.map f_s) (a2 := jr_s)
      (b := blockOutObjects s) (c := balObjects s)).mp
      (by simpa [fixedObjects, f_s, jr_s] using hW.2.2.1.2)
    have hd_buf : IvlsDisj [(p, 16 * ntx)]
        ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
          ("keccak_pad", 136), ("keccak_st", 200)].map (bufferRegion s)) := by
      intro x hx y hy
      simp only [List.mem_singleton] at hx; subst hx
      obtain ⟨gn, hgn_in, rfl⟩ := List.mem_map.1 hy
      have hgn_gb : gn ∈ globalBuffers := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hgn_in
        rcases hgn_in with rfl | rfl | rfl | rfl <;> decide
      have hm_gb : bufferRegion s gn ∈ globalBuffers.map f_s :=
        List.mem_map.2 ⟨gn, hgn_gb, rfl⟩
      have hd_full : Disj (bufferRegion s gn) (p, 16 * ntx + 16) :=
        hF_parts.2.1 _ hm_gb _ (List.mem_append_right _ (List.mem_append_left _ hbo_mem))
      have hin_p : Inside (p, 16 * ntx) p (p + (16 * ntx + 16)) := ⟨le_rfl, by dsimp only; omega⟩
      exact (disj_of_inside_right hin_p hd_full).flip
    exact ⟨hin_sub, hw_sub, hp8, by omega, hd_buf⟩

private theorem hoare_while_ncb_condFalse {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {cond : ExpHOL 64} {body : ProgHOL 64}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hncb : noContBreak body = true)
    (hbody : Hoare (fun s => P s ∧ CondTrue cond s) body (fun r t => r = none → P t)) :
    Hoare P (.while cond body) (fun r t => r = none → P t ∧ CondFalse cond t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.while cond body) with ⟨r, post⟩
  rw [hrun] at hr
  dsimp only at hr
  subst hr
  suffices ∀ (k : Nat) (st : PanSemStateFiniteExact 64 F),
      st.clock = k → st.code = originalRuntimeCode → P st →
      evaluateHOLFiniteState st (.while cond body) = (none, post) → P post ∧ CondFalse cond post from
    this s.clock s rfl hcode hP hrun
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro st hk st_code hPst hst_run
    rw [evaluateHOLFiniteState_while_total] at hst_run
    split at hst_run
    · rename_i w hw
      split at hst_run
      · rename_i hwnz
        split at hst_run
        · simp at hst_run
        · dsimp only at hst_run
          rw [fixClockHOLFinite_evaluateState] at hst_run
          have hrem := evaluateHOLFiniteState_clock_le (decClockHOLFinite st) body
          have hmeta := (evaluateHOLFiniteState_metadata (decClockHOLFinite st) body).1
          have hct : CondTrue cond (decClockHOLFinite st) := by
            obtain ⟨_, hw', hwnz'⟩ := loopActive_decClock (s := st) ⟨w, hw, hwnz⟩
            refine ⟨_, ?_, hwnz'⟩
            rw [← evalHOLFinite_eq_toExact]
            exact hw'
          have hn := noContBreak_sound body hncb (decClockHOLFinite st)
          rcases bRun : evaluateHOLFiniteState (decClockHOLFinite st) body with ⟨r1, mid⟩
          rw [bRun] at hst_run hrem hmeta hn
          have hclk_lt : mid.clock < k := by
            change mid.clock ≤ st.clock - 1 at hrem
            omega
          have hb_nt : (evaluateHOLFiniteState (decClockHOLFinite st) body).1 ≠ some .timeOut := by
            intro hto
            rw [bRun] at hto; dsimp only at hto; subst hto
            simp at hst_run
          have hb_post := hbody.run (decClockHOLFinite st) st_code ⟨hdec st hPst, hct⟩ hb_nt
          rw [bRun] at hb_post
          dsimp only at hb_post
          cases r1 with
          | none =>
            exact ih mid.clock hclk_lt mid rfl (hmeta.trans st_code) (hb_post rfl) hst_run
          | some r1' =>
            cases r1' with
            | «continue» => exact absurd rfl hn.1
            | «break» => exact absurd rfl hn.2
            | _ => simp at hst_run
      · rename_i hwz
        simp at hst_run
        obtain ⟨_, rfl⟩ := hst_run
        refine ⟨hPst, ?_⟩
        unfold CondFalse
        rw [← evalHOLFinite_eq_toExact]
        have hw0 : w = 0#64 := Decidable.not_not.1 hwz
        subst hw0
        exact hw
    · simp at hst_run

private theorem hoare_call_none_fall {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} {arguments : List (ExpHOL 64)}
    (hf : FunSpec Pc Qc fname) (hentry : CallEntryOn P Pc fname arguments)
    (hret : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F)
      (callee : HolFiniteMapExact MlS (ValueHOL 64)) (post : PanSemStateFiniteExact 64 F)
      (v : ValueHOL 64), s.code = originalRuntimeCode → P s →
      Qc (callEntryStateHOLFinite s callee) (some (.returned v)) post →
      Q { post with locals := s.locals }) :
    Hoare P (.call (some (none, none)) fname arguments) (fun r t => r = none → Q t) :=
  Hoare.call0 hf hentry (fun s callee post v hcode hP hQc _ => hret s callee post v hcode hP hQc)
    (fun _ _ hr _ h => absurd h hr)

private theorem seq_skip_on {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64} {B : Nat}
    (hp : TerminatingProgBoundedOn P prog B) :
    TerminatingProgBoundedOn P (.seq .skip prog) (0 + B) :=
  TerminatingProgBoundedOn.seq_hoare (straight_on _ rfl) (Hoare.skip fun _ h _ => h) hp

private theorem hoare_seq_skip {P Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {prog : ProgHOL 64}
    (hp : Hoare P prog (fun r t => r = none → Q t)) :
    Hoare P (.seq .skip prog) (fun r t => r = none → Q t) :=
  Hoare.seq_fall (Hoare.skip fun _ h _ => h) hp

private def PostLoopBase (need64 : Bool) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 80) = w_ntx.toNat ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    BlockSliceLengths s w_ntx.toNat ∧
    (need64 = true → memW s (globN s "bo" + 64) = 0)

private def PostLoopWithBal : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => PostLoopBase false s ∧
    ∃ a b : BitVec 64, s.locals.lookup (ofString "bal") = some (.rStruct [.val (.word a), .val (.word b)])

private def PostLoopWithOut (outName : String) (sz : Nat) :
    ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs w_out a b : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    s.locals.lookup (ofString "bal") = some (.rStruct [.val (.word a), .val (.word b)]) ∧
    s.locals.lookup (ofString outName) = some (.val (.word w_out)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 80) = w_ntx.toNat ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    BlockSliceLengths s w_ntx.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat [(w_out.toNat, sz)]

private theorem postLoopBase_worldOK {need64 : Bool} {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : PostLoopBase need64 s) : WorldOK s := by
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := h
  exact blockContext_worldOK hc

private theorem postLoopBase_guestInv {need64 : Bool} {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : PostLoopBase need64 s) : GuestInv s :=
  worldOK_guestInv s (postLoopBase_worldOK s h)

private theorem postLoopBase_reqsFresh {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : PostLoopBase true s) : ReqsFresh s := by
  obtain ⟨_, _, _, _, _, _, _, _, hc, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h64⟩ := h
  exact ⟨blockContext_worldOK hc, h64 rfl⟩

private theorem postLoopWithBal_worldOK {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : PostLoopWithBal s) : WorldOK s :=
  postLoopBase_worldOK s h.1

private theorem postLoopWithBal_guestInv {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : PostLoopWithBal s) : GuestInv s :=
  worldOK_guestInv s (postLoopWithBal_worldOK s h)

private theorem postLoopWithOut_worldOK {outName : String} {sz : Nat} {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : PostLoopWithOut outName sz s) : WorldOK s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hc, _⟩ := h
  exact blockContext_worldOK hc

private theorem postLoopWithOut_guestInv {outName : String} {sz : Nat} {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : PostLoopWithOut outName sz s) : GuestInv s :=
  worldOK_guestInv s (postLoopWithOut_worldOK s h)

private theorem localsOnly_postLoopBase (need64 : Bool) :
    LocalsOnly ["si", "hdr", "pl", "ntx", "txs", "rcs"] (PostLoopBase need64) := by
  intro F s locals k hl h
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h80, hin_txs, hin_rcs, hsl, h64⟩ := h
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd,
    (blockContext_with_locals s locals k S Nd w_si.toNat w_hdr.toNat).2 hc,
    (hl "si" (by simp)).trans hsi,
    (hl "hdr" (by simp)).trans hhdr,
    (hl "pl" (by simp)).trans hpl,
    (hl "ntx" (by simp)).trans hntx,
    (hl "txs" (by simp)).trans htxs,
    (hl "rcs" (by simp)).trans hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h80, hin_txs, hin_rcs,
    (blockSliceLengths_with_locals s locals k w_ntx.toNat).2 hsl, h64⟩

private theorem localsOnly_postLoopWithBal :
    LocalsOnly ["si", "hdr", "pl", "ntx", "txs", "rcs", "bal"] PostLoopWithBal := by
  intro F s locals k hl ⟨hbase, a, b, hbal⟩
  refine ⟨localsOnly_postLoopBase false s locals k
    (fun n hn => hl n (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hn ⊢; tauto)) hbase,
    a, b, (hl "bal" (by simp)).trans hbal⟩

private theorem bufferList16_disj_worldTypedIvls {F : Type}
    (s : PanSemStateFiniteExact 64 F) {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) :
    (∀ j ∈ [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
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
            (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)],
        j.2 = 0 → j.1 % 8 = 0) ∧
    IvlsDisj
      [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
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
       (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)]
      (worldTypedIvls s S Nd) ∧
    ∀ {bs : List Ivl}, TrackedBlocks s S Nd bs →
      IvlsDisj bs
        [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
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
         (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)] := by
  have hbuf0 : ∀ (g : String) (sz : Nat), sz ≠ 0 →
      (bufferRegion s (g, sz)).2 = 0 → (bufferRegion s (g, sz)).1 % 8 = 0 :=
    fun g sz hsz => bufferRegion_zero_aligned s g sz hsz
  have hdisj_tb : ∀ {bs : List Ivl}, TrackedBlocks s S Nd bs →
      ∀ (gn : String × Nat), gn ∈ globalBuffers → ∀ n, n ≤ gn.2 →
      ∀ b ∈ bs, Disj b (bufferRegion s (gn.1, n)) := by
    intro bs hbs gn hgn n hle b hb
    have hd := (hbs b hb).2.2.2.2 (bufferRegion s gn) (bufferRegion_mem_worldOwned s S Nd hgn)
    by_cases hz : globN s gn.1 = 0
    · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
    · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
      unfold Disj at hd ⊢; dsimp only at hd ⊢; omega
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    change i ∈ [bufferRegion s ("b2_v", 128), bufferRegion s ("bal_key_buf", 64),
      bufferRegion s ("bn_expw", 352), bufferRegion s ("bn_gamma", 384),
      bufferRegion s ("evm_key_buf", 32), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("mpt_nib_scratch", 64),
      bufferRegion s ("pre_hdr_buf", 96), bufferRegion s ("rmd_h", 40),
      bufferRegion s ("rmd_pad", 128), bufferRegion s ("rmd_x", 128),
      bufferRegion s ("sha_pad", 128), bufferRegion s ("sha_st", 64),
      bufferRegion s ("sk_buf", 52), bufferRegion s ("u256_ws", 640)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact hbuf0 _ _ (by omega)
  · intro i hi j hj
    change i ∈ [bufferRegion s ("b2_v", 128), bufferRegion s ("bal_key_buf", 64),
      bufferRegion s ("bn_expw", 352), bufferRegion s ("bn_gamma", 384),
      bufferRegion s ("evm_key_buf", 32), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("mpt_nib_scratch", 64),
      bufferRegion s ("pre_hdr_buf", 96), bufferRegion s ("rmd_h", 40),
      bufferRegion s ("rmd_pad", 128), bufferRegion s ("rmd_x", 128),
      bufferRegion s ("sha_pad", 128), bufferRegion s ("sha_st", 64),
      bufferRegion s ("sk_buf", 52), bufferRegion s ("u256_ws", 640)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bufferRegion_disj_le hWT ("b2_v", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("bal_key_buf", 64) (by decide) (by decide) 64 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("bn_expw", 352) (by decide) (by decide) 352 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("bn_gamma", 384) (by decide) (by decide) 384 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("evm_key_buf", 32) (by decide) (by decide) 32 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("mpt_nib_scratch", 64) (by decide) (by decide) 64 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("pre_hdr_buf", 96) (by decide) (by decide) 96 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("rmd_h", 40) (by decide) (by decide) 40 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("rmd_pad", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("rmd_x", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("sha_pad", 128) (by decide) (by decide) 128 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("sha_st", 64) (by decide) (by decide) 64 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("sk_buf", 64) (by decide) (by decide) 52 (by decide) j hj
    · exact bufferRegion_disj_le hWT ("u256_ws", 640) (by decide) (by decide) 640 le_rfl j hj
  · intro bs hbs b hb i hi
    change i ∈ [bufferRegion s ("b2_v", 128), bufferRegion s ("bal_key_buf", 64),
      bufferRegion s ("bn_expw", 352), bufferRegion s ("bn_gamma", 384),
      bufferRegion s ("evm_key_buf", 32), bufferRegion s ("keccak_pad", 136),
      bufferRegion s ("keccak_st", 200), bufferRegion s ("mpt_nib_scratch", 64),
      bufferRegion s ("pre_hdr_buf", 96), bufferRegion s ("rmd_h", 40),
      bufferRegion s ("rmd_pad", 128), bufferRegion s ("rmd_x", 128),
      bufferRegion s ("sha_pad", 128), bufferRegion s ("sha_st", 64),
      bufferRegion s ("sk_buf", 52), bufferRegion s ("u256_ws", 640)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hdisj_tb hbs ("b2_v", 128) (by decide) 128 le_rfl b hb
    · exact hdisj_tb hbs ("bal_key_buf", 64) (by decide) 64 le_rfl b hb
    · exact hdisj_tb hbs ("bn_expw", 352) (by decide) 352 le_rfl b hb
    · exact hdisj_tb hbs ("bn_gamma", 384) (by decide) 384 le_rfl b hb
    · exact hdisj_tb hbs ("evm_key_buf", 32) (by decide) 32 le_rfl b hb
    · exact hdisj_tb hbs ("keccak_pad", 136) (by decide) 136 le_rfl b hb
    · exact hdisj_tb hbs ("keccak_st", 200) (by decide) 200 le_rfl b hb
    · exact hdisj_tb hbs ("mpt_nib_scratch", 64) (by decide) 64 le_rfl b hb
    · exact hdisj_tb hbs ("pre_hdr_buf", 96) (by decide) 96 le_rfl b hb
    · exact hdisj_tb hbs ("rmd_h", 40) (by decide) 40 le_rfl b hb
    · exact hdisj_tb hbs ("rmd_pad", 128) (by decide) 128 le_rfl b hb
    · exact hdisj_tb hbs ("rmd_x", 128) (by decide) 128 le_rfl b hb
    · exact hdisj_tb hbs ("sha_pad", 128) (by decide) 128 le_rfl b hb
    · exact hdisj_tb hbs ("sha_st", 64) (by decide) 64 le_rfl b hb
    · exact hdisj_tb hbs ("sk_buf", 64) (by decide) 52 (by decide) b hb
    ·       exact hdisj_tb hbs ("u256_ws", 640) (by decide) 640 le_rfl b hb

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
      rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
      simp only [valueIsWord, Bool.and_self, ↓reduceIte, List.map, valueWord, wordOpHOL, wordOp,
        List.foldr, add_zero, Option.map, Option.some.injEq, ValueHOL.val.injEq,
        HolWordLab.word.injEq] at hev
      exact ⟨w1, w2, h1, h2, hev.symm⟩

private theorem bufferList5_pw_disj {F : Type}
    (s : PanSemStateFiniteExact 64 F) {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) :
    (∀ j ∈ [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
            (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
            (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
            (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)],
        j.2 = 0 → j.1 % 8 = 0) ∧
    IvlsDisj
      [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
       (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
       (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
       (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
       (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)]
      (worldTypedIvls s S Nd) ∧
    ∀ {bs : List Ivl}, TrackedBlocks s S Nd bs →
      IvlsDisj bs
        [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
         (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)] := by
  obtain ⟨h0, h1, h2⟩ := bufferList16_disj_worldTypedIvls s hWT
  have hsub : ∀ i ∈ [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
      (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
      (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
      (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)],
      i ∈ [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
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
           (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)] := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp
  exact ⟨fun j hj => h0 j (hsub j hj),
    fun j hj y hy => h1 j (hsub j hj) y hy,
    fun hbs b hb j hj => h2 hbs b hb j (hsub j hj)⟩

private theorem bufferList4_csr_disj {F : Type}
    (s : PanSemStateFiniteExact 64 F) {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) :
    (∀ j ∈ [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
            (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
            (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)],
        j.2 = 0 → j.1 % 8 = 0) ∧
    IvlsDisj
      [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
       (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
       (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
       (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]
      (worldTypedIvls s S Nd) ∧
    ∀ {bs : List Ivl}, TrackedBlocks s S Nd bs →
      IvlsDisj bs
        [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
         (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)] := by
  have hbuf0 : ∀ (g : String) (sz : Nat), sz ≠ 0 →
      (bufferRegion s (g, sz)).2 = 0 → (bufferRegion s (g, sz)).1 % 8 = 0 :=
    fun g sz hsz => bufferRegion_zero_aligned s g sz hsz
  have hdisj_tb : ∀ {bs : List Ivl}, TrackedBlocks s S Nd bs →
      ∀ (gn : String × Nat), gn ∈ globalBuffers → ∀ n, n ≤ gn.2 →
      ∀ b ∈ bs, Disj b (bufferRegion s (gn.1, n)) := by
    intro bs hbs gn hgn n hle b hb
    have hd := (hbs b hb).2.2.2.2 (bufferRegion s gn) (bufferRegion_mem_worldOwned s S Nd hgn)
    by_cases hz : globN s gn.1 = 0
    · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
    · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
      unfold Disj at hd ⊢; dsimp only at hd ⊢; omega
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    change i ∈ [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_hash_scratch", 40), bufferRegion s ("mpt_nib_scratch", 64)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact hbuf0 _ _ (by omega)
  · intro i hi j hj
    change i ∈ [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_hash_scratch", 40), bufferRegion s ("mpt_nib_scratch", 64)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact bufferRegion_disj_le hWT ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("mpt_hash_scratch", 40) (by decide) (by decide) 40 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("mpt_nib_scratch", 64) (by decide) (by decide) 64 le_rfl j hj
  · intro bs hbs b hb i hi
    change i ∈ [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_hash_scratch", 40), bufferRegion s ("mpt_nib_scratch", 64)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hdisj_tb hbs ("keccak_pad", 136) (by decide) 136 le_rfl b hb
    · exact hdisj_tb hbs ("keccak_st", 200) (by decide) 200 le_rfl b hb
    · exact hdisj_tb hbs ("mpt_hash_scratch", 40) (by decide) 40 le_rfl b hb
    · exact hdisj_tb hbs ("mpt_nib_scratch", 64) (by decide) 64 le_rfl b hb

private theorem bufferList4_mpt_disj {F : Type}
    (s : PanSemStateFiniteExact 64 F) {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) :
    (∀ j ∈ [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
            (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
            (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)],
        j.2 = 0 → j.1 % 8 = 0) ∧
    IvlsDisj
      [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
       (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
       (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
       (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)]
      (worldTypedIvls s S Nd) ∧
    ∀ {bs : List Ivl}, TrackedBlocks s S Nd bs →
      IvlsDisj bs
        [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
         (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)] := by
  have hbuf0 : ∀ (g : String) (sz : Nat), sz ≠ 0 →
      (bufferRegion s (g, sz)).2 = 0 → (bufferRegion s (g, sz)).1 % 8 = 0 :=
    fun g sz hsz => bufferRegion_zero_aligned s g sz hsz
  have hdisj_tb : ∀ {bs : List Ivl}, TrackedBlocks s S Nd bs →
      ∀ (gn : String × Nat), gn ∈ globalBuffers → ∀ n, n ≤ gn.2 →
      ∀ b ∈ bs, Disj b (bufferRegion s (gn.1, n)) := by
    intro bs hbs gn hgn n hle b hb
    have hd := (hbs b hb).2.2.2.2 (bufferRegion s gn) (bufferRegion_mem_worldOwned s S Nd hgn)
    by_cases hz : globN s gn.1 = 0
    · exact Or.inr (Or.inl (by simp [bufferRegion, hz]))
    · simp only [bufferRegion, hz, ↓reduceIte] at hd ⊢
      unfold Disj at hd ⊢; dsimp only at hd ⊢; omega
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    change i ∈ [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_hash_scratch", 40), bufferRegion s ("mpt_key_scratch", 16)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> exact hbuf0 _ _ (by omega)
  · intro i hi j hj
    change i ∈ [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_hash_scratch", 40), bufferRegion s ("mpt_key_scratch", 16)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact bufferRegion_disj_le hWT ("keccak_pad", 136) (by decide) (by decide) 136 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("keccak_st", 200) (by decide) (by decide) 200 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("mpt_hash_scratch", 40) (by decide) (by decide) 40 le_rfl j hj
    · exact bufferRegion_disj_le hWT ("mpt_key_scratch", 16) (by decide) (by decide) 16 le_rfl j hj
  · intro bs hbs b hb i hi
    change i ∈ [bufferRegion s ("keccak_pad", 136), bufferRegion s ("keccak_st", 200),
      bufferRegion s ("mpt_hash_scratch", 40), bufferRegion s ("mpt_key_scratch", 16)] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact hdisj_tb hbs ("keccak_pad", 136) (by decide) 136 le_rfl b hb
    · exact hdisj_tb hbs ("keccak_st", 200) (by decide) 200 le_rfl b hb
    · exact hdisj_tb hbs ("mpt_hash_scratch", 40) (by decide) 40 le_rfl b hb
    · exact hdisj_tb hbs ("mpt_key_scratch", 16) (by decide) 16 le_rfl b hb

private theorem bufferList2_lb_disj {F : Type}
    (s : PanSemStateFiniteExact 64 F) {S Nd : List Nat} (hWT : WorldTypedWith s S Nd) :
    (∀ j ∈ [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
            (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
        j.2 = 0 → j.1 % 8 = 0) ∧
    IvlsDisj
      [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
       (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)]
      (worldTypedIvls s S Nd) ∧
    ∀ {bs : List Ivl}, TrackedBlocks s S Nd bs →
      IvlsDisj bs
        [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)] := by
  obtain ⟨h0, h1, h2⟩ := bufferList4_mpt_disj s hWT
  have hsub : ∀ i ∈ [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
      (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)],
      i ∈ [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
           (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
           (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
           (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)] := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    rcases hi with rfl | rfl <;> simp
  exact ⟨fun j hj => h0 j (hsub j hj),
    fun j hj y hy => h1 j (hsub j hj) y hy,
    fun hbs b hb j hj => h2 hbs b hb j (hsub j hj)⟩

private theorem evalAt_op_word {F : Type} {s : PanSemStateFiniteExact 64 F}
    {op : BinOp} {es : List (ExpHOL 64)} {v : ValueHOL 64}
    (hev : evalAt s (.op op es) = some v) :
    ∃ w : BitVec 64, v = .val (.word w) := by
  simp only [evalAt, evalHOLExact] at hev
  rcases hl : @evalListHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) es with _ | vs
  · rw [hl] at hev; simp at hev
  · rw [hl] at hev; dsimp only at hev
    split at hev
    · simp only [Option.map] at hev
      rcases hw : wordOpHOL op (vs.map valueWord) with _ | w
      · rw [hw] at hev; simp at hev
      · rw [hw] at hev; exact ⟨w, (Option.some.inj hev).symm⟩
    · simp at hev

private theorem hoare_assign_bal_index_postLoop :
    Hoare (PostLoopBase true)
      (.assign .global (ofString "bal_index") (.op .add [.var .local (ofString "ntx"), .const 1#64]))
      (fun r t => r = none → PostLoopBase true t) := by
  apply Hoare.assign_fall
  intro F s v hP hev
  dsimp only [setKvarHOLFinite]
  obtain ⟨w, rfl⟩ := evalAt_op_word hev
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h80, hin_txs, hin_rcs, hsl, h64⟩ := hP
  obtain ⟨hc', _⟩ := blockContext_setGlobal_bal_index (w := w) hc
    (by simp [TrackedBlocks] : TrackedBlocks s S Nd [])
  have hbo_eq : globN (setGlobalHOLFinite (ofString "bal_index") (.val (.word w)) s) "bo" = globN s "bo" :=
    globN_setGlobal_ne s (ofString "bal_index") (.val (.word w)) "bo" (by decide)
  have hhp_eq : globN (setGlobalHOLFinite (ofString "bal_index") (.val (.word w)) s) "heap_ptr" = globN s "heap_ptr" :=
    globN_setGlobal_ne s (ofString "bal_index") (.val (.word w)) "heap_ptr" (by decide)
  refine ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc', hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, by rw [hbo_eq]; exact hbo_nz, htxs_nz, hrcs_nz,
    by change memW _ (globN _ "bo" + 24) = w_txs.toNat; rw [hbo_eq]; exact h24,
    by change memW _ (globN _ "bo" + 32) = w_rcs.toNat; rw [hbo_eq]; exact h32,
    by change memW _ (globN _ "bo" + 80) = w_ntx.toNat; rw [hbo_eq]; exact h80,
    by rw [hhp_eq]; exact hin_txs, by rw [hhp_eq]; exact hin_rcs, ?_,
    fun ht => by change memW _ (globN _ "bo" + 64) = 0; rw [hbo_eq]; exact h64 ht⟩
  unfold BlockSliceLengths
  rw [hbo_eq]
  exact hsl

private theorem hoare_process_withdrawals_postLoop
    (wpw : WorldKeeps WorldOK
      (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "process_withdrawals")) :
    Hoare (PostLoopBase true)
      (.call (some (none, none)) (ofString "process_withdrawals") [.var .local (ofString "pl")])
      (fun r t => r = none → PostLoopBase true t) := by
  refine hoare_call_none_fall wpw
    (callEntryOn_of_imp localsFree_worldOK postLoopBase_worldOK _ _) ?_
  intro F s callee post v _ hP hQc
  have hws := hQc (Or.inl ⟨v, rfl⟩)
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h80, hin_txs, hin_rcs, hsl, h64⟩ := hP
  set ce := callEntryStateHOLFinite s callee
  have hc_ce : BlockContext ce S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  obtain ⟨hR0, hRtyped, hRtb⟩ := bufferList5_pw_disj ce hc_ce.world
  obtain ⟨S', Nd', hc_post, _, hu_reg, _, hq⟩ :=
    blockContext_worldStep hc_ce (by simp [TrackedBlocks] : TrackedBlocks ce S Nd []) hws
      (by decide) (by decide) (by decide) (by decide)
      hR0 hRtyped (hRtb hc_ce.regions) (fun hnz => hRtb (hc_ce.hashes hnz)) (by simp [IvlsDisj])
  have h24_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 24)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
  have h32_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 32)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
  have h64_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 64)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
  have h80_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 80)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
  have hsl_post : BlockSliceLengths post w_ntx.toNat :=
    blockSliceLengths_of_retBoSlicesKept (S := S') (Nd := Nd') hsl
      (by change w_ntx.toNat ≤ memW s (globN s "bo" + 80); omega) hq rfl
  refine ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S', Nd',
    (blockContext_with_locals post s.locals post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    hsi, hhdr, hpl, hntx, htxs, hrcs,
    by change w_pl.toNat = memW post w_si.toNat; rw [hsi0_eq]; exact hpl_eq,
    by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le,
    by change globN post "bo" ≠ 0; rw [h24_eq.1]; exact hbo_nz,
    htxs_nz, hrcs_nz,
    by change memW post (globN post "bo" + 24) = w_txs.toNat; rw [h24_eq.2]; exact h24,
    by change memW post (globN post "bo" + 32) = w_rcs.toNat; rw [h32_eq.2]; exact h32,
    by change memW post (globN post "bo" + 80) = w_ntx.toNat; rw [h80_eq.2]; exact h80,
    ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩,
    ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩,
    hsl_post,
    fun ht => by change memW post (globN post "bo" + 64) = 0; rw [h64_eq.2]; exact h64 ht⟩

private theorem hoare_process_gpr_postLoop
    (wgpr : WorldKeeps ReqsFresh
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
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 72, 80])]
      RetBoSlicesKept (ofString "process_general_purpose_requests")) :
    Hoare (PostLoopBase true)
      (.call (some (none, none)) (ofString "process_general_purpose_requests") [])
      (fun r t => r = none → PostLoopBase false t) := by
  have hLF_rf : LocalsFree ReqsFresh :=
    fun s locals k ⟨hW, h64⟩ => ⟨localsFree_worldOK s locals k hW, h64⟩
  refine hoare_call_none_fall wgpr
    (callEntryOn_of_imp hLF_rf postLoopBase_reqsFresh _ _) ?_
  intro F s callee post v _ hP hQc
  have hws := hQc (Or.inl ⟨v, rfl⟩)
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h80, hin_txs, hin_rcs, hsl, _⟩ := hP
  set ce := callEntryStateHOLFinite s callee
  have hc_ce : BlockContext ce S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  obtain ⟨hR0, hRtyped, hRtb⟩ := bufferList16_disj_worldTypedIvls ce hc_ce.world
  obtain ⟨S', Nd', hc_post, _, hu_reg, _, hq⟩ :=
    blockContext_worldStep hc_ce (by simp [TrackedBlocks] : TrackedBlocks ce S Nd []) hws
      (by decide) (by decide) (by decide) (by decide)
      hR0 hRtyped (hRtb hc_ce.regions) (fun hnz => hRtb (hc_ce.hashes hnz)) (by simp [IvlsDisj])
  have h24_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 72, 80]) (off := 24)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
  have h32_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 72, 80]) (off := 32)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
  have h80_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 72, 80]) (off := 80)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
  have hsl_post : BlockSliceLengths post w_ntx.toNat :=
    blockSliceLengths_of_retBoSlicesKept (S := S') (Nd := Nd') hsl
      (by change w_ntx.toNat ≤ memW s (globN s "bo" + 80); omega) hq rfl
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S', Nd',
    (blockContext_with_locals post s.locals post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    hsi, hhdr, hpl, hntx, htxs, hrcs,
    by change w_pl.toNat = memW post w_si.toNat; rw [hsi0_eq]; exact hpl_eq,
    by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le,
    by change globN post "bo" ≠ 0; rw [h24_eq.1]; exact hbo_nz,
    htxs_nz, hrcs_nz,
    by change memW post (globN post "bo" + 24) = w_txs.toNat; rw [h24_eq.2]; exact h24,
    by change memW post (globN post "bo" + 32) = w_rcs.toNat; rw [h32_eq.2]; exact h32,
    by change memW post (globN post "bo" + 80) = w_ntx.toNat; rw [h80_eq.2]; exact h80,
    ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩,
    ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩,
    hsl_post,
    fun h => by cases h⟩

private theorem resumeOn_build_bal_rlp_shaped
    (wbal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "build_block_access_list_rlp")) :
    ∀ {F : Type} (state : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
      (value : ValueHOL 64) (post : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode → PostLoopBase false state →
      evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [] = some values →
      lookupCodeHOLFinite state.code.lookup (ofString "build_block_access_list_rlp") values =
        some (body, callee, returnShape) →
      evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body =
        (some (.returned value), post) →
      shapeEqHOL (shapeOfHOLExact value) (.comb [.one, .one]) = true →
      PostLoopWithBal (setVarHOLFinite (ofString "bal") value { post with locals := state.locals }) := by
  intro F s values body callee ret value post hcode hP _ hl hrun hsh
  have hW_ce : WorldOK (callEntryStateHOLFinite s callee) :=
    localsFree_worldOK s callee (s.clock - 1) (postLoopBase_worldOK s hP)
  have hstep := FunSpec.at_lookup wbal s hcode values body callee ret hl hW_ce (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h80, hin_txs, hin_rcs, hsl, _⟩ := hP
  set ce := callEntryStateHOLFinite s callee
  have hc_ce : BlockContext ce S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  obtain ⟨S', Nd', hc_post, _, hu_reg, _, hq⟩ :=
    blockContext_worldStep_nil hc_ce (by simp [TrackedBlocks] : TrackedBlocks ce S Nd []) hws
      (by decide) (by decide) (by decide) (by decide)
  have h24_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 24)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp) (by simp [IvlsDisj])
  have h32_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 32)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp) (by simp [IvlsDisj])
  have h80_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 80)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp) (by simp [IvlsDisj])
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
  have hsl_post : BlockSliceLengths post w_ntx.toNat :=
    blockSliceLengths_of_retBoSlicesKept (S := S') (Nd := Nd') hsl
      (by change w_ntx.toNat ≤ memW s (globN s "bo" + 80); omega) hq rfl
  have hbase_res : PostLoopBase false (setVarHOLFinite (ofString "bal") value { post with locals := s.locals }) := by
    refine ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S', Nd',
      (blockContext_with_locals post _ post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bal" ≠ ofString "si" by decide, hsi],
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bal" ≠ ofString "hdr" by decide, hhdr],
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bal" ≠ ofString "pl" by decide, hpl],
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bal" ≠ ofString "ntx" by decide, hntx],
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bal" ≠ ofString "txs" by decide, htxs],
      by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "bal" ≠ ofString "rcs" by decide, hrcs],
      by change w_pl.toNat = memW post w_si.toNat; rw [hsi0_eq]; exact hpl_eq,
      by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
      hntx_le,
      by change globN post "bo" ≠ 0; rw [h24_eq.1]; exact hbo_nz,
      htxs_nz, hrcs_nz,
      by change memW post (globN post "bo" + 24) = w_txs.toNat; rw [h24_eq.2]; exact h24,
      by change memW post (globN post "bo" + 32) = w_rcs.toNat; rw [h32_eq.2]; exact h32,
      by change memW post (globN post "bo" + 80) = w_ntx.toNat; rw [h80_eq.2]; exact h80,
      ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩,
      ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩,
      hsl_post,
      fun h => by cases h⟩
  have hsh_eq := (shapeEqHOL_eq_true _ _).1 hsh
  cases value with
  | val _ => simp [shapeOfHOLExact] at hsh_eq
  | nStruct _ _ => simp [shapeOfHOLExact] at hsh_eq
  | rStruct vs =>
    simp only [shapeOfHOLExact, ShapeHOL.comb.injEq] at hsh_eq
    rcases vs with _ | ⟨v0, _ | ⟨v1, _ | _⟩⟩ <;> simp at hsh_eq
    rcases hsh_eq with ⟨hv0, hv1⟩
    cases v0 with
    | rStruct _ => simp [shapeOfHOLExact] at hv0
    | nStruct _ _ => simp [shapeOfHOLExact] at hv0
    | val wl0 =>
      cases wl0 with
      | word a =>
        cases v1 with
        | rStruct _ => simp [shapeOfHOLExact] at hv1
        | nStruct _ _ => simp [shapeOfHOLExact] at hv1
        | val wl1 =>
          cases wl1 with
          | word b =>
            exact ⟨hbase_res, a, b, by simp [setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]⟩

private theorem hoare_validate_bal_gas_limit_postLoop
    (hro : ReadOnlyFn (ofString "validate_block_access_list_gas_limit")) :
    Hoare PostLoopWithBal
      (.call (some (none, none)) (ofString "validate_block_access_list_gas_limit")
        [.load .one (.op .add [.var .global (ofString "be"), .const 8#64])])
      (fun r t => r = none → PostLoopWithBal t) := by
  refine hoare_call_none_fall hro
    (callEntryOn_of_imp localsFree_guestInv postLoopWithBal_guestInv _ _) ?_
  intro F s callee post v _ hP hQc
  have hro_eq := hQc (Or.inl ⟨v, rfl⟩)
  have heq : ({ post with locals := s.locals } : PanSemStateFiniteExact 64 F) =
      { s with locals := s.locals, clock := post.clock } := by
    rw [hro_eq]; rfl
  rw [heq]
  exact localsOnly_postLoopWithBal s s.locals post.clock (fun _ _ => rfl) hP

private theorem resumeOn_alloc_postLoopOut (outName : String) (sz : Nat)
    (hsz8 : sz % 8 = 0) (hsz_lt : sz < 2 ^ 64)
    (hne : ∀ n ∈ (["si", "hdr", "pl", "ntx", "txs", "rcs", "bal"] : List String),
      ofString outName ≠ ofString n)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn PostLoopWithBal (PostLoopWithOut outName sz)
      (ofString outName) (ofString "alloc") [.const (BitVec.ofNat 64 sz)] := by
  intro F s values body callee ret value post hcode ⟨hbase, a, b, hbal⟩ hargs hl hrun
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h80, hin_txs, hin_rcs, hsl, _⟩ := hbase
  have hpc := callee_param_one_exp s (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc) (.const (BitVec.ofNat 64 sz))
    (.val (.word (BitVec.ofNat 64 sz))) values body callee ret rfl hargs hl
  have hn_loc : locN (callEntryStateHOLFinite s callee) "n" = sz := by
    simp only [locN, callEntryStateHOLFinite, hpc.2, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hsz_lt
  have hround : (sz + 7) / 8 * 8 = sz := by omega
  have hW_ce : WorldOK (callEntryStateHOLFinite s callee) :=
    localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc)
  have hstep := FunSpec.at_lookup wal s hcode values body callee ret hl hW_ce (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal s hcode values body callee ret hl
    (localsFree_arenaReady s callee (s.clock - 1) hc.arena) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_out, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hmbe := alloc_call_mem_be_eq hcode hc.arena hl hrun
  have hmemW_eq : ∀ addr : Nat, memW post addr = memW s addr := by
    intro addr; unfold memW; rw [hmbe.1]
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (hws.2.2.1 _ (by decide : ofString "bo" ∉ ["heap_ptr"].map ofString))
  have hc_ce : BlockContext (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  have hws' : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ p => [(p, (sz + 7) / 8 * 8)]))
      (callEntryStateHOLFinite s callee) (some (.returned (.val (.word w_out)))) post := by
    refine ⟨hws.1, hws.2.1, hws.2.2.1, hws.2.2.2.1, ?_⟩
    intro S₀ Nd₀ hWT₀ hDisj₀
    obtain ⟨S', Nd', hsub, hWT', hOg', hFo', hQ'⟩ := hws.2.2.2.2 S₀ Nd₀ hWT₀ hDisj₀
    refine ⟨S', Nd', hsub, hWT', hOg', hFo', ?_⟩
    intro v hv
    obtain ⟨w', hw', hd'⟩ := hQ' v hv
    dsimp only at hd' ⊢
    exact ⟨w', hw', by rwa [hn_loc] at hd'⟩
  obtain ⟨S', Nd', hc_post, htd_post, _, _, _⟩ :=
    trackedDisjIn_alloc_result hc_ce trackedDisjIn_nil hfb hws'
  rw [List.nil_append, hround] at htd_post
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
  have hsl_post : BlockSliceLengths post w_ntx.toNat := by
    constructor
    · change SliceLengthsBelow post (memW post (globN post "bo" + 24)) w_ntx.toNat
      rw [hbo_eq, hmemW_eq]
      exact sliceLengthsBelow_transfer hsl.1 (fun _ _ => hmemW_eq _)
    · change SliceLengthsBelow post (memW post (globN post "bo" + 32)) w_ntx.toNat
      rw [hbo_eq, hmemW_eq]
      exact sliceLengthsBelow_transfer hsl.2 (fun _ _ => hmemW_eq _)
  set resumed := setVarHOLFinite (ofString outName) (.val (.word w_out)) { post with locals := s.locals }
  have htd_res : TrackedDisjIn resumed S' Nd' w_si.toNat w_hdr.toNat [(w_out.toNat, sz)] := by
    obtain ⟨h1, h2, h3, h4⟩ := htd_post
    exact ⟨(trackedBlocks_with_locals post _ post.clock S' Nd' _).2 h1, h2, h3, h4⟩
  refine ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_out, a, b, S', Nd',
    (blockContext_with_locals post _ post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne "si" (by simp), hsi],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne "hdr" (by simp), hhdr],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne "pl" (by simp), hpl],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne "ntx" (by simp), hntx],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne "txs" (by simp), htxs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne "rcs" (by simp), hrcs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, hne "bal" (by simp), hbal],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by change w_pl.toNat = memW post w_si.toNat; rw [hmemW_eq]; exact hpl_eq,
    by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hmemW_eq]; exact hntx_eq,
    hntx_le,
    by change globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
    htxs_nz, hrcs_nz,
    by change memW post (globN post "bo" + 24) = w_txs.toNat; rw [hbo_eq, hmemW_eq]; exact h24,
    by change memW post (globN post "bo" + 32) = w_rcs.toNat; rw [hbo_eq, hmemW_eq]; exact h32,
    by change memW post (globN post "bo" + 80) = w_ntx.toNat; rw [hbo_eq, hmemW_eq]; exact h80,
    ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩,
    ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩,
    hsl_post,
    htd_res⟩

private theorem hoare_out_call_postLoop (outName : String) (sz : Nat)
    (fname : MlS) (arguments : List (ExpHOL 64))
    (Rbuf : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl)
    (gw : List String)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hjc_gw : ofString "journal_cap" ∉ gw.map ofString)
    (hbh_gw : ofString "block_hashes" ∉ gw.map ofString)
    (hbhn_gw : ofString "block_hashes_n" ∉ gw.map ofString)
    (hwd_gw : ofString "wd_rlp_slices" ∉ gw.map ofString)
    (_hRbuf_loc : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (c : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat),
      Rbuf { s with locals := c, clock := k } = Rbuf s)
    (hRbuf : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) {S Nd : List Nat}, WorldTypedWith s S Nd →
      (∀ j ∈ Rbuf s, j.2 = 0 → j.1 % 8 = 0) ∧
      IvlsDisj (Rbuf s) (worldTypedIvls s S Nd) ∧
      (∀ {bs : List Ivl}, TrackedBlocks s S Nd bs → IvlsDisj bs (Rbuf s)))
    (hout_bind : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret : ShapeHOL) (w_out : BitVec 64),
      s.code = originalRuntimeCode →
      PostLoopWithOut outName sz s →
      s.locals.lookup (ofString outName) = some (.val (.word w_out)) →
      evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments = some values →
      lookupCodeHOLFinite s.code.lookup fname values = some (body, callee, ret) →
      callee.lookup (ofString "out") = some (.val (.word w_out)))
    (wk : WorldKeeps WorldOK (fun s => (locN s "out", sz) :: Rbuf s) gw
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept fname) :
    Hoare (PostLoopWithOut outName sz)
      (.call (some (none, none)) fname arguments)
      (fun r t => r = none → PostLoopWithBal t) := by
  refine ⟨fun {F} s hcode hP hnt hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s (.call (some (none, none)) fname arguments) with ⟨r, post0⟩
  rw [hrun] at hr hnt; dsimp only at hr; subst hr
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body, callee, ret⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      split at hrun
      · simp at hrun
      · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, post⟩
        rw [hb] at hrun
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hrun
              rw [← hpost_eq]
              have hP_copy := hP
              obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_out, a, b, S, Nd,
                hc, hsi, hhdr, hpl, hntx, htxs, hrcs, hbal, hout_s,
                hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h80,
                hin_txs, hin_rcs, hsl, htd_out⟩ := hP
              have hcout := hout_bind s values body callee ret w_out hcode hP_copy hout_s hargs hl
              set ce := callEntryStateHOLFinite s callee
              have hout_ce : locN ce "out" = w_out.toNat := by
                simp [ce, locN, callEntryStateHOLFinite, hcout]
              have hW_ce : WorldOK ce :=
                localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc)
              have hstep := FunSpec.at_lookup wk s hcode values body callee ret hl hW_ce
                (by rw [hb]; simp)
              rw [hb] at hstep; dsimp only at hstep
              have hws := hstep (Or.inl ⟨v, rfl⟩)
              have hc_ce : BlockContext ce S Nd w_si.toNat w_hdr.toNat :=
                (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
              obtain ⟨hR0_b, hRtyped_b, hRtb_b⟩ := hRbuf ce hc_ce.world
              have htb_out_ce : TrackedBlocks ce S Nd [(w_out.toNat, sz)] :=
                (trackedBlocks_with_locals s callee (s.clock - 1) S Nd _).2 htd_out.1
              have hout_prop := htb_out_ce (w_out.toNat, sz) (by simp)
              have hR0 : ∀ j ∈ (locN ce "out", sz) :: Rbuf ce, j.2 = 0 → j.1 % 8 = 0 := by
                intro j hj hj0
                rcases List.mem_cons.1 hj with rfl | hj'
                · rw [hout_ce]; exact hout_prop.1
                · exact hR0_b j hj' hj0
              have hRtyped : IvlsDisj ((locN ce "out", sz) :: Rbuf ce) (worldTypedIvls ce S Nd) := by
                intro j hj y hy
                rcases List.mem_cons.1 hj with rfl | hj'
                · rw [hout_ce]
                  exact hout_prop.2.2.2.2 y (worldTypedIvls_sub_worldOwned ce S Nd y hy)
                · exact hRtyped_b j hj' y hy
              have hRreg : IvlsDisj (inputRegions ce w_si.toNat w_hdr.toNat) ((locN ce "out", sz) :: Rbuf ce) := by
                intro c hcm j hj
                rcases List.mem_cons.1 hj with rfl | hj'
                · rw [hout_ce]
                  exact htd_out.2.2.1 c hcm _ (by simp)
                · exact hRtb_b hc_ce.regions c hcm j hj'
              have hRhash : globN ce "block_hashes_n" ≠ 0 →
                  IvlsDisj [(globN ce "block_hashes", 32 * globN ce "block_hashes_n")]
                    ((locN ce "out", sz) :: Rbuf ce) := by
                intro hnz c hcm j hj
                rcases List.mem_cons.1 hj with rfl | hj'
                · rw [hout_ce]
                  exact htd_out.2.2.2 hnz c hcm _ (by simp)
                · exact hRtb_b (hc_ce.hashes hnz) c hcm j hj'
              obtain ⟨S', Nd', hc_post, _, hu_reg, _, hq⟩ :=
                blockContext_worldStep hc_ce (by simp [TrackedBlocks] : TrackedBlocks ce S Nd []) hws
                  hjc_gw hwd_gw hbh_gw hbhn_gw hR0 hRtyped hRreg hRhash (by simp [IvlsDisj])
              have h24_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 24)
                hc_ce.arena.2 hc_ce.world hbo_nz hws hbo_gw (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
              have h32_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 32)
                hc_ce.arena.2 hc_ce.world hbo_nz hws hbo_gw (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
              have h80_eq := bo_slot_eq_of_worldStep (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 80)
                hc_ce.arena.2 hc_ce.world hbo_nz hws hbo_gw (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
              have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
                  c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
                fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
              have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
                simpa only [Nat.add_zero] using
                  inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
                    (off := 0) (by omega) (by omega)
              have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
                inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
                  (off := 40) (by omega) (by omega)
              have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
              have hsl_post : BlockSliceLengths post w_ntx.toNat :=
                blockSliceLengths_of_retBoSlicesKept (S := S') (Nd := Nd') hsl
                  (by change w_ntx.toNat ≤ memW s (globN s "bo" + 80); omega) hq rfl
              exact ⟨⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S', Nd',
                (blockContext_with_locals post s.locals post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
                hsi, hhdr, hpl, hntx, htxs, hrcs,
                by change w_pl.toNat = memW post w_si.toNat; rw [hsi0_eq]; exact hpl_eq,
                by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
                hntx_le,
                by change globN post "bo" ≠ 0; rw [h24_eq.1]; exact hbo_nz,
                htxs_nz, hrcs_nz,
                by change memW post (globN post "bo" + 24) = w_txs.toNat; rw [h24_eq.2]; exact h24,
                by change memW post (globN post "bo" + 32) = w_rcs.toNat; rw [h32_eq.2]; exact h32,
                by change memW post (globN post "bo" + 80) = w_ntx.toNat; rw [h80_eq.2]; exact h80,
                ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩,
                ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩,
                hsl_post,
                fun h => by cases h⟩, a, b, hbal⟩
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

private theorem hoare_compute_state_root_postLoop
    (wcsr : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "compute_state_root")) :
    Hoare (PostLoopWithOut "root" 32)
      (.call (some (none, none)) (ofString "compute_state_root") [.var .local (ofString "root")])
      (fun r t => r = none → PostLoopWithBal t) := by
  refine hoare_out_call_postLoop "root" 32 (ofString "compute_state_root") [.var .local (ofString "root")]
    (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
               (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
               (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
               (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
    ["heap_ptr", "scratch_ptr"]
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ => rfl)
    bufferList4_csr_disj
    ?_ wcsr
  intro F s values body callee ret w_out hcode _ hout_s hargs hl
  exact (callee_param_one_exp s (ofString "compute_state_root") (ofString "out") .one _ _
    (by rw [hcode]; exact lookup_compute_state_root_fn) (.var .local (ofString "root"))
    (.val (.word w_out)) values body callee ret
    (by simp [evalAt, evalHOLExact, hout_s]) hargs hl).2

private def PostBloom : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_hdr w_pl : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    w_pl.toNat = memW s w_si.toNat

private def PostBloomWithWroot : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s => ∃ w_si w_hdr w_pl w_out : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "wroot") = some (.val (.word w_out)) ∧
    w_pl.toNat = memW s w_si.toNat

private theorem postBloom_guestInv {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : PostBloom s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, hc, _⟩ := h
  exact hc.arena.1

private theorem postBloomWithWroot_guestInv {F : Type}
    (s : PanSemStateFiniteExact 64 F) (h : PostBloomWithWroot s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hc, _⟩ := h
  exact hc.arena.1

private theorem resumeOn_alloc_postBloomWroot
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn PostBloom PostBloomWithWroot
      (ofString "wroot") (ofString "alloc") [.const 32#64] := by
  intro F s values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, w_hdr, w_pl, S, Nd, hc, hsi, hhdr, hpl, hpl_eq⟩ := hP
  have hpc := callee_param_one_exp s (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc) (.const 32#64)
    (.val (.word 32#64)) values body callee ret rfl hargs hl
  have hn_loc : locN (callEntryStateHOLFinite s callee) "n" = 32 := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hW_ce : WorldOK (callEntryStateHOLFinite s callee) :=
    localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc)
  have hstep := FunSpec.at_lookup wal s hcode values body callee ret hl hW_ce (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal s hcode values body callee ret hl
    (localsFree_arenaReady s callee (s.clock - 1) hc.arena) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_out, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hmbe := alloc_call_mem_be_eq hcode hc.arena hl hrun
  have hmemW_eq : ∀ addr : Nat, memW post addr = memW s addr := by
    intro addr; unfold memW; rw [hmbe.1]
  have hc_ce : BlockContext (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  have hws' : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ p => [(p, (32 + 7) / 8 * 8)]))
      (callEntryStateHOLFinite s callee) (some (.returned (.val (.word w_out)))) post := by
    refine ⟨hws.1, hws.2.1, hws.2.2.1, hws.2.2.2.1, ?_⟩
    intro S₀ Nd₀ hWT₀ hDisj₀
    obtain ⟨S', Nd', hsub, hWT', hOg', hFo', hQ'⟩ := hws.2.2.2.2 S₀ Nd₀ hWT₀ hDisj₀
    refine ⟨S', Nd', hsub, hWT', hOg', hFo', ?_⟩
    intro v hv
    obtain ⟨w', hw', hd'⟩ := hQ' v hv
    dsimp only at hd' ⊢
    exact ⟨w', hw', by rwa [hn_loc] at hd'⟩
  obtain ⟨S', Nd', hc_post, _, _, _, _⟩ :=
    trackedDisjIn_alloc_result hc_ce trackedDisjIn_nil hfb hws'
  set resumed := setVarHOLFinite (ofString "wroot") (.val (.word w_out)) { post with locals := s.locals }
  exact ⟨w_si, w_hdr, w_pl, w_out, S', Nd',
    (blockContext_with_locals post _ post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, (by decide : ofString "wroot" ≠ ofString "si"), hsi],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, (by decide : ofString "wroot" ≠ ofString "hdr"), hhdr],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, (by decide : ofString "wroot" ≠ ofString "pl"), hpl],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by change w_pl.toNat = memW post w_si.toNat; rw [hmemW_eq]; exact hpl_eq⟩

private theorem hoare_guestInv_of_imp {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (himp : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → GuestInv s)
    (prog : ProgHOL 64) :
    Hoare P prog (fun r t => r = none → GuestInv t) :=
  ⟨fun s hcode hP hnt _ => preservesOn_guestInv prog s hcode (himp s hP) hnt⟩

private theorem hoare_logs_bloom_postLoop
    (wlb : WorldKeeps WorldOK
      (fun s => [(locN s "out", 256),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "logs_bloom")) :
    Hoare (PostLoopWithOut "bloom" 256)
      (.call (some (none, none)) (ofString "logs_bloom")
        [.load .one (.op .add [.var .global (ofString "bo"), .const 40#64]),
         .var .local (ofString "bloom")])
      (fun r t => r = none → PostBloom t) := by
  refine ⟨fun {F} s hcode hP hnt hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "logs_bloom")
        [.load .one (.op .add [.var .global (ofString "bo"), .const 40#64]),
         .var .local (ofString "bloom")]) with ⟨r, post0⟩
  rw [hrun] at hr hnt; dsimp only at hr; subst hr
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "bo"), .const 40#64]),
       .var .local (ofString "bloom")] with _ | values
  · rw [hargs] at hrun; simp at hrun
  · rw [hargs] at hrun; dsimp only at hrun
    rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "logs_bloom") values with _ | ⟨body, callee, ret⟩
    · rw [hl] at hrun; simp at hrun
    · rw [hl] at hrun; dsimp only at hrun
      split at hrun
      · simp at hrun
      · rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, post⟩
        rw [hb] at hrun
        cases bres with
        | none => simp at hrun
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hrun
            split at hrun
            · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hrun
              rw [← hpost_eq]
              obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_out, a, b, S, Nd,
                hc, hsi, hhdr, hpl, _, _, _, _, hout_s,
                hpl_eq, _, _, _, _, _, _, _, _,
                _, _, _, htd_out⟩ := hP
              have hargs' := hargs
              rw [evalListHOLFinite_eq_toExact] at hargs'
              simp only [evalListHOLExact] at hargs'
              rcases he1 : @evalHOLExact 64 F _ s.toExact
                  (fun a => Classical.propDecidable (s.memaddrs a))
                  (.load .one (.op .add [.var .global (ofString "bo"), .const 40#64])) with _ | v1
              · rw [he1] at hargs'; simp at hargs'
              · have hcout : callee.lookup (ofString "out") = some (.val (.word w_out)) :=
                  (callee_param_two s (ofString "logs_bloom") (ofString "logs") (ofString "out") .one .one _ _
                    (by rw [hcode]; exact lookup_logs_bloom_fn)
                    (.load .one (.op .add [.var .global (ofString "bo"), .const 40#64]))
                    (.var .local (ofString "bloom")) v1 (.val (.word w_out)) values body callee ret
                    he1 (by simp [evalAt, evalHOLExact, hout_s]) hargs hl).2.2
                set ce := callEntryStateHOLFinite s callee
                have hout_ce : locN ce "out" = w_out.toNat := by
                  simp [ce, locN, callEntryStateHOLFinite, hcout]
                have hW_ce : WorldOK ce :=
                  localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc)
                have hstep := FunSpec.at_lookup wlb s hcode values body callee ret hl hW_ce
                  (by rw [hb]; simp)
                rw [hb] at hstep; dsimp only at hstep
                have hws := hstep (Or.inl ⟨v, rfl⟩)
                have hc_ce : BlockContext ce S Nd w_si.toNat w_hdr.toNat :=
                  (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
                obtain ⟨hR0_b, hRtyped_b, hRtb_b⟩ := bufferList2_lb_disj ce hc_ce.world
                have htb_out_ce : TrackedBlocks ce S Nd [(w_out.toNat, 256)] :=
                  (trackedBlocks_with_locals s callee (s.clock - 1) S Nd _).2 htd_out.1
                have hout_prop := htb_out_ce (w_out.toNat, 256) (by simp)
                have hR0 : ∀ j ∈ (locN ce "out", 256) :: [(globN ce "keccak_pad", if globN ce "keccak_pad" = 0 then 0 else 136),
                    (globN ce "keccak_st", if globN ce "keccak_st" = 0 then 0 else 200)], j.2 = 0 → j.1 % 8 = 0 := by
                  intro j hj hj0
                  rcases List.mem_cons.1 hj with rfl | hj'
                  · rw [hout_ce]; exact hout_prop.1
                  · exact hR0_b j hj' hj0
                have hRtyped : IvlsDisj ((locN ce "out", 256) :: [(globN ce "keccak_pad", if globN ce "keccak_pad" = 0 then 0 else 136),
                    (globN ce "keccak_st", if globN ce "keccak_st" = 0 then 0 else 200)]) (worldTypedIvls ce S Nd) := by
                  intro j hj y hy
                  rcases List.mem_cons.1 hj with rfl | hj'
                  · rw [hout_ce]
                    exact hout_prop.2.2.2.2 y (worldTypedIvls_sub_worldOwned ce S Nd y hy)
                  · exact hRtyped_b j hj' y hy
                have hRreg : IvlsDisj (inputRegions ce w_si.toNat w_hdr.toNat)
                    ((locN ce "out", 256) :: [(globN ce "keccak_pad", if globN ce "keccak_pad" = 0 then 0 else 136),
                    (globN ce "keccak_st", if globN ce "keccak_st" = 0 then 0 else 200)]) := by
                  intro c hcm j hj
                  rcases List.mem_cons.1 hj with rfl | hj'
                  · rw [hout_ce]
                    exact htd_out.2.2.1 c hcm _ (by simp)
                  · exact hRtb_b hc_ce.regions c hcm j hj'
                have hRhash : globN ce "block_hashes_n" ≠ 0 →
                    IvlsDisj [(globN ce "block_hashes", 32 * globN ce "block_hashes_n")]
                      ((locN ce "out", 256) :: [(globN ce "keccak_pad", if globN ce "keccak_pad" = 0 then 0 else 136),
                      (globN ce "keccak_st", if globN ce "keccak_st" = 0 then 0 else 200)]) := by
                  intro hnz c hcm j hj
                  rcases List.mem_cons.1 hj with rfl | hj'
                  · rw [hout_ce]
                    exact htd_out.2.2.2 hnz c hcm _ (by simp)
                  · exact hRtb_b (hc_ce.hashes hnz) c hcm j hj'
                obtain ⟨S', Nd', hc_post, _, hu_reg, _, _⟩ :=
                  blockContext_worldStep hc_ce (by simp [TrackedBlocks] : TrackedBlocks ce S Nd []) hws
                    (by decide) (by decide) (by decide) (by decide) hR0 hRtyped hRreg hRhash (by simp [IvlsDisj])
                have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
                    c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
                  fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
                have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
                  simpa only [Nat.add_zero] using
                    inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
                      (off := 0) (by omega) (by omega)
                exact ⟨w_si, w_hdr, w_pl, S', Nd',
                  (blockContext_with_locals post s.locals post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
                  hsi, hhdr, hpl,
                  by change w_pl.toNat = memW post w_si.toNat; rw [hsi0_eq]; exact hpl_eq⟩
            · simp at hrun
          | _ => simp [emptyLocalsHOLFinite] at hrun

private theorem hoare_build_mpt_indexed_postLoop (outName : String) (e1 e2 : ExpHOL 64)
    (wbmi : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
                 (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "build_mpt_indexed")) :
    Hoare (PostLoopWithOut outName 32)
      (.call (some (none, none)) (ofString "build_mpt_indexed") [e1, e2, .var .local (ofString outName)])
      (fun r t => r = none → PostLoopWithBal t) := by
  refine hoare_out_call_postLoop outName 32 (ofString "build_mpt_indexed")
    [e1, e2, .var .local (ofString outName)]
    (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
               (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
               (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
               (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
    ["heap_ptr", "scratch_ptr"]
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (fun _ _ _ => rfl)
    bufferList4_mpt_disj
    ?_ wbmi
  intro F s values body callee ret w_out hcode _ hout_s hargs hl
  have hargs' := hargs
  rw [evalListHOLFinite_eq_toExact] at hargs'
  simp only [evalListHOLExact] at hargs'
  rcases he1 : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · rw [he1] at hargs'; simp at hargs'
  · rw [he1] at hargs'
    rcases he2 : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · rw [he2] at hargs'; simp at hargs'
    · exact (callee_param_three s (ofString "build_mpt_indexed")
        (ofString "slice_arr") (ofString "n") (ofString "out") .one .one .one _ _
        (by rw [hcode]; exact lookup_build_mpt_indexed_fn)
        e1 e2 (.var .local (ofString outName)) v1 v2 (.val (.word w_out)) values body callee ret
        he1 he2 (by simp [evalAt, evalHOLExact, hout_s]) hargs hl).2.2

private theorem callEntryOn_build_mpt_indexed_bo (arrName outName : String) (off : Nat)
    (hoff : off ∈ ([24, 32] : List Nat))
    (hsel : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) (w_txs w_rcs : BitVec 64),
      s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) →
      s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) →
      memW s (globN s "bo" + 24) = w_txs.toNat →
      memW s (globN s "bo" + 32) = w_rcs.toNat →
      s.locals.lookup (ofString arrName) = some (.val (.word (if off = 24 then w_txs else w_rcs))) ∧
      memW s (globN s "bo" + off) = (if off = 24 then w_txs else w_rcs).toNat ∧
      (Inside (w_txs.toNat, 16 * (locN s "ntx") + 16) sourceBase (globN s "heap_ptr") →
       Inside (w_rcs.toNat, 16 * (locN s "ntx") + 16) sourceBase (globN s "heap_ptr") →
       Inside ((if off = 24 then w_txs else w_rcs).toNat, 16 * (locN s "ntx") + 16) sourceBase (globN s "heap_ptr"))) :
    CallEntryOn (PostLoopWithOut outName 32) BuildMptIndexedReady (ofString "build_mpt_indexed")
      [.var .local (ofString arrName), .var .local (ofString "ntx"), .var .local (ofString outName)] := by
  intro F s values body callee ret hcode hP hargs hl
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_out, a, b, S, Nd,
    hc, hsi, hhdr, hpl, hntx, htxs, hrcs, hbal, hout,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h80,
    hin_txs, hin_rcs, hsl, _⟩ := hP
  obtain ⟨harr, hbo_off, hin_sel⟩ := hsel s w_txs w_rcs htxs hrcs h24 h32
  set w_arr := if off = 24 then w_txs else w_rcs
  have hntx_loc : locN s "ntx" = w_ntx.toNat := by simp [locN, hntx]
  have hin_arr_full : Inside (memW s (globN s "bo" + off), 16 * memW s (globN s "bo" + 80) + 16)
      sourceBase (globN s "heap_ptr") := by
    rw [hbo_off, h80, ← hntx_loc]
    exact hin_sel (by rwa [hntx_loc]) (by rwa [hntx_loc])
  have hp_nz : memW s (globN s "bo" + off) ≠ 0 := by
    rw [hbo_off]
    rcases List.mem_cons.1 hoff with rfl | hoff'
    · simp [w_arr, htxs_nz]
    · have hoff32 := List.mem_singleton.1 hoff'
      simp [w_arr, hoff32, hrcs_nz]
  obtain ⟨hin_sub, hw_sub, _, _, hd_buf⟩ :=
    bo_array_sub_allocated_wordsOK hc.arena hc.world hbo_nz hoff hp_nz hin_arr_full
  have hp3 := callee_param_three s (ofString "build_mpt_indexed")
    (ofString "slice_arr") (ofString "n") (ofString "out") .one .one .one _ _
    (by rw [hcode]; exact lookup_build_mpt_indexed_fn)
    (.var .local (ofString arrName)) (.var .local (ofString "ntx")) (.var .local (ofString outName))
    (.val (.word w_arr)) (.val (.word w_ntx)) (.val (.word w_out)) values body callee ret
    (by simp [evalAt, evalHOLExact, harr])
    (by simp [evalAt, evalHOLExact, hntx])
    (by simp [evalAt, evalHOLExact, hout]) hargs hl
  set ce := callEntryStateHOLFinite s callee
  have hsarr_ce : locN ce "slice_arr" = memW s (globN s "bo" + off) := by
    simp [ce, locN, callEntryStateHOLFinite, hp3.1, hbo_off]
  have hn_ce : locN ce "n" = memW s (globN s "bo" + 80) := by
    simp [ce, locN, callEntryStateHOLFinite, hp3.2.1, h80]
  have hsl_arr : SliceLengthsBelow s (memW s (globN s "bo" + off)) (memW s (globN s "bo" + 80)) := by
    rw [h80]
    rcases List.mem_cons.1 hoff with rfl | hoff'
    · exact hsl.1
    · rw [List.mem_singleton.1 hoff']; exact hsl.2
  refine buildMptIndexedReady_of_sliceLengths
    (localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc))
    (fun name hname => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
      rcases hname with rfl | rfl | rfl
      · exact ⟨w_arr, hp3.1⟩
      · exact ⟨w_ntx, hp3.2.1⟩
      · exact ⟨w_out, hp3.2.2⟩)
    (by rw [hn_ce, h80]; omega)
    (by rw [hsarr_ce, hn_ce]; exact hin_sub)
    (by rw [hsarr_ce, hn_ce]; exact hw_sub)
    (by rw [hsarr_ce, hn_ce]; exact hd_buf)
    (by rw [hsarr_ce, hn_ce]; exact hsl_arr)

private theorem callEntryOn_build_mpt_indexed_txs :
    CallEntryOn (PostLoopWithOut "txroot" 32) BuildMptIndexedReady (ofString "build_mpt_indexed")
      [.var .local (ofString "txs"), .var .local (ofString "ntx"), .var .local (ofString "txroot")] :=
  callEntryOn_build_mpt_indexed_bo "txs" "txroot" 24 (by simp)
    (fun _ _ _ htxs _ h24 _ => ⟨by simp [htxs], by simp [h24], fun h1 _ => by simpa using h1⟩)

private theorem callEntryOn_build_mpt_indexed_rcs :
    CallEntryOn (PostLoopWithOut "rroot" 32) BuildMptIndexedReady (ofString "build_mpt_indexed")
      [.var .local (ofString "rcs"), .var .local (ofString "ntx"), .var .local (ofString "rroot")] :=
  callEntryOn_build_mpt_indexed_bo "rcs" "rroot" 32 (by simp)
    (fun _ _ _ _ hrcs _ h32 => ⟨by simp [hrcs], by simp [h32], fun _ h2 => by simpa using h2⟩)

private theorem callEntryOn_build_mpt_indexed_wds :
    CallEntryOn PostBloomWithWroot BuildMptIndexedReady (ofString "build_mpt_indexed")
      [.var .global (ofString "wd_rlp_slices"),
       .load .one (.op .add [.var .local (ofString "pl"), .const 56#64]),
       .var .local (ofString "wroot")] := by
  intro F s values body callee ret hcode hP hargs hl
  obtain ⟨w_si, w_hdr, w_pl, w_out, S, Nd, hc, hsi, hhdr, hpl, hout, hpl_eq⟩ := hP
  have hg_s : GuestInv s := hc.arena.1
  have hargs' := hargs
  rw [evalListHOLFinite_eq_toExact] at hargs'
  simp only [evalListHOLExact] at hargs'
  rcases he1 : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) (.var .global (ofString "wd_rlp_slices")) with _ | v1
  · rw [he1] at hargs'; simp at hargs'
  · rw [he1] at hargs'
    rcases he2 : @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a))
        (.load .one (.op .add [.var .local (ofString "pl"), .const 56#64])) with _ | v2
    · rw [he2] at hargs'; simp at hargs'
    · obtain ⟨w_wd, hw_wd_gl⟩ := hc.arena.2.2.2.2.2.2.2.2.2 "wd_rlp_slices" (by decide)
      have hv1 : v1 = .val (.word w_wd) := by
        simp only [evalHOLExact, PanSemStateFiniteExact.toExact, GlobalWord] at he1 hw_wd_gl
        rw [hw_wd_gl] at he1
        exact (Option.some.inj he1).symm
      subst hv1
      obtain ⟨a56, w_nwd, ha56, rfl, hw_nwd_eq, _, _, _⟩ := evalAt_load_one_word hg_s he2
      obtain ⟨w1, w2, hw1, hw2, ha56_eq⟩ := evalAt_add2_words ha56
      have hw1_eq : w_pl = w1 := by
        simp only [evalAt, evalHOLExact, PanSemStateFiniteExact.toExact, hpl, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hw1
        exact hw1
      have hw2_eq : w2 = 56#64 := by
        simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq] at hw2
        exact hw2.symm
      subst hw1_eq; subst hw2_eq; subst ha56_eq
      have hpl_reg := hc.regions (memW s w_si.toNat, 136) (by simp [inputRegions])
      have hpl_bound : memW s w_si.toNat + 136 ≤ 2 ^ 64 :=
        hpl_reg.2.2.1.2.trans (hc.arena.2.2.1.trans (by decide))
      have ha56_nat : (w_pl + 56#64).toNat = memW s w_si.toNat + 56 := by
        rw [BitVec.toNat_add, hpl_eq]
        change (memW s w_si.toNat + 56) % 2 ^ 64 = memW s w_si.toNat + 56
        exact Nat.mod_eq_of_lt (by omega)
      rw [ha56_nat] at hw_nwd_eq
      have hp3 := callee_param_three s (ofString "build_mpt_indexed")
        (ofString "slice_arr") (ofString "n") (ofString "out") .one .one .one _ _
        (by rw [hcode]; exact lookup_build_mpt_indexed_fn)
        (.var .global (ofString "wd_rlp_slices"))
        (.load .one (.op .add [.var .local (ofString "pl"), .const 56#64]))
        (.var .local (ofString "wroot"))
        (.val (.word w_wd)) (.val (.word w_nwd)) (.val (.word w_out)) values body callee ret
        he1 he2 (by simp [evalAt, evalHOLExact, hout]) hargs hl
      set ce := callEntryStateHOLFinite s callee
      have hwd_glob : globN s "wd_rlp_slices" = w_wd.toNat := by simp [globN, GlobalWord] at hw_wd_gl ⊢; simp [hw_wd_gl]
      have hsarr_ce : locN ce "slice_arr" = globN s "wd_rlp_slices" := by
        simp [ce, locN, callEntryStateHOLFinite, hp3.1, hwd_glob]
      have hn_ce : locN ce "n" = memW s (memW s w_si.toNat + 56) := by
        simp [ce, locN, callEntryStateHOLFinite, hp3.2.1, hw_nwd_eq]
      have hwd_reg := hc.regions (globN s "wd_rlp_slices", 16 * memW s (memW s w_si.toNat + 56))
        (by simp [inputRegions])
      have hd_buf : IvlsDisj [(globN s "wd_rlp_slices", 16 * memW s (memW s w_si.toNat + 56))]
          ([("mpt_hash_scratch", 40), ("mpt_key_scratch", 16),
            ("keccak_pad", 136), ("keccak_st", 200)].map (bufferRegion ce)) := by
        obtain ⟨_, _, hRtb⟩ := bufferList4_mpt_disj s hc.world
        have hwd_tb : TrackedBlocks s S Nd [(globN s "wd_rlp_slices", 16 * memW s (memW s w_si.toNat + 56))] :=
          fun b hb => by rw [List.mem_singleton.1 hb]; exact hwd_reg
        have hd4 := hRtb hwd_tb
        intro x hx y hy
        obtain ⟨gn, hgn_in, rfl⟩ := List.mem_map.1 hy
        have hbr_eq : bufferRegion ce gn = bufferRegion s gn := rfl
        rw [hbr_eq]
        apply hd4 x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hgn_in ⊢
        rcases hgn_in with rfl | rfl | rfl | rfl <;> simp [bufferRegion]
      exact buildMptIndexedReady_of_sliceLengths
        (localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc))
        (fun name hname => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hname
          rcases hname with rfl | rfl | rfl
          · exact ⟨w_wd, hp3.1⟩
          · exact ⟨w_nwd, hp3.2.1⟩
          · exact ⟨w_out, hp3.2.2⟩)
        (by rw [hn_ce]; exact hc.nwd_32)
        (by rw [hsarr_ce, hn_ce]; exact hwd_reg.2.2.1)
        (by rw [hsarr_ce, hn_ce]; exact hwd_reg.2.2.2.1)
        (by rw [hsarr_ce, hn_ce]; exact hd_buf)
        (by rw [hsarr_ce, hn_ce]; exact hc.wd_slices)

private def progExecBlockPostLoop : ProgHOL 64 :=
  .seq (.assign .global (ofString "bal_index") (.op .add [.var .local (ofString "ntx"), .const 1#64]))
    (.seq .skip
      (.seq (.call (some (none, none)) (ofString "process_withdrawals") [.var .local (ofString "pl")])
        (.seq .skip
          (.seq (.call (some (none, none)) (ofString "process_general_purpose_requests") [])
            (.seq .skip
              (.decCall (ofString "bal") (.comb [.one, .one]) (ofString "build_block_access_list_rlp") []
                (.seq
                  (.call (some (none, none)) (ofString "validate_block_access_list_gas_limit")
                    [.load .one (.op .add [.var .global (ofString "be"), .const 8#64])])
                  (.seq .skip
                    (.decCall (ofString "root") .one (ofString "alloc") [.const 32#64]
                      (.seq
                        (.call (some (none, none)) (ofString "compute_state_root") [.var .local (ofString "root")])
                        (.seq .skip
                          (.decCall (ofString "txroot") .one (ofString "alloc") [.const 32#64]
                            (.seq
                              (.call (some (none, none)) (ofString "build_mpt_indexed")
                                [.var .local (ofString "txs"), .var .local (ofString "ntx"), .var .local (ofString "txroot")])
                              (.decCall (ofString "rroot") .one (ofString "alloc") [.const 32#64]
                                (.seq
                                  (.call (some (none, none)) (ofString "build_mpt_indexed")
                                    [.var .local (ofString "rcs"), .var .local (ofString "ntx"), .var .local (ofString "rroot")])
                                  (.decCall (ofString "bloom") .one (ofString "alloc") [.const 256#64]
                                    (.seq
                                      (.call (some (none, none)) (ofString "logs_bloom")
                                        [.load .one (.op .add [.var .global (ofString "bo"), .const 40#64]),
                                         .var .local (ofString "bloom")])
                                      (.decCall (ofString "wroot") .one (ofString "alloc") [.const 32#64]
                                        (.seq
                                          (.call (some (none, none)) (ofString "build_mpt_indexed")
                                            [.var .global (ofString "wd_rlp_slices"),
                                             .load .one (.op .add [.var .local (ofString "pl"), .const 56#64]),
                                             .var .local (ofString "wroot")])
                                          progExecBlockGuestTail)))))))))))))))))))

private def kExecBlockPostLoop : Nat :=
  (K.«process_withdrawals» + 1) + (K.«process_general_purpose_requests» + 1) +
    (K.«build_block_access_list_rlp» + 1) + (K.«validate_block_access_list_gas_limit» + 1) +
    (K.«alloc» + 1) + (K.«compute_state_root» + 1) +
    (K.«alloc» + 1) + (K.«build_mpt_indexed» + 1) +
    (K.«alloc» + 1) + (K.«build_mpt_indexed» + 1) +
    (K.«alloc» + 1) + (K.«logs_bloom» + 1) +
    (K.«alloc» + 1) + (K.«build_mpt_indexed» + 1) +
    kExecBlockGuestTail

private theorem terminating_progExecBlockPostLoop
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hbal_rlp : TerminatingFunBoundedOn GuestInv (ofString "build_block_access_list_rlp") K.«build_block_access_list_rlp»)
    (hbmi : TerminatingFunBoundedOn BuildMptIndexedReady (ofString "build_mpt_indexed") K.«build_mpt_indexed»)
    (hcrh : TerminatingFunBoundedOn GuestInv (ofString "compute_requests_hash") K.«compute_requests_hash»)
    (hcsr : TerminatingFunBoundedOn WorldOK (ofString "compute_state_root") K.«compute_state_root»)
    (hkec : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hlb : TerminatingFunBoundedOn GuestInv (ofString "logs_bloom") K.«logs_bloom»)
    (hmax : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max»)
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hgpr : TerminatingFunBoundedOn ReqsFresh (ofString "process_general_purpose_requests") K.«process_general_purpose_requests»)
    (hpw : TerminatingFunBoundedOn WorldOK (ofString "process_withdrawals") K.«process_withdrawals»)
    (hvbal : TerminatingFunBoundedOn GuestInv (ofString "validate_block_access_list_gas_limit") K.«validate_block_access_list_gas_limit»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wbal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "build_block_access_list_rlp"))
    (wbmi : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
                 (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "build_mpt_indexed"))
    (wcsr : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "compute_state_root"))
    (wlb : WorldKeeps WorldOK
      (fun s => [(locN s "out", 256),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "logs_bloom"))
    (wgpr : WorldKeeps ReqsFresh
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
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 72, 80])]
      RetBoSlicesKept (ofString "process_general_purpose_requests"))
    (wpw : WorldKeeps WorldOK
      (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "process_withdrawals"))
    (hro_vbal : ReadOnlyFn (ofString "validate_block_access_list_gas_limit")) :
    TerminatingProgBoundedOn (PostLoopBase true) progExecBlockPostLoop kExecBlockPostLoop := by
  unfold progExecBlockPostLoop
  have hLF_rf : LocalsFree ReqsFresh :=
    fun s locals k ⟨hW, h64⟩ => ⟨localsFree_worldOK s locals k hW, h64⟩
  have htail_gi : TerminatingProgBoundedOn GuestInv progExecBlockGuestTail kExecBlockGuestTail :=
    terminating_progExecBlockGuestTail hal hcrh hkec hmax hmeq
  have hbody : TerminatingProgBoundedOn (PostLoopBase true) _
      (0 + (0 + (K.process_withdrawals + 1 + (0 + (K.process_general_purpose_requests + 1 +
        (0 + (K.build_block_access_list_rlp + (K.validate_block_access_list_gas_limit + 1 +
          (0 + (K.alloc + (K.compute_state_root + 1 + (0 + (K.alloc + (K.build_mpt_indexed + 1 +
            (K.alloc + (K.build_mpt_indexed + 1 + (K.alloc + (K.logs_bloom + 1 +
              (K.alloc + (K.build_mpt_indexed + 1 + kExecBlockGuestTail) + 1)) + 1)) + 1)) + 1))) + 1))) + 1))))))) :=
    TerminatingProgBoundedOn.seq_hoare
      (straight_on _ rfl)
      hoare_assign_bal_index_postLoop
      (seq_skip_on
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.call_on hpw none [.var .local (ofString "pl")]
            (callEntryOn_of_imp localsFree_worldOK (postLoopBase_worldOK (need64 := true)) _ _))
          (hoare_process_withdrawals_postLoop wpw)
          (seq_skip_on
            (TerminatingProgBoundedOn.seq_hoare_trans
              (TerminatingProgBoundedOn.call_on hgpr none []
                (callEntryOn_of_imp hLF_rf postLoopBase_reqsFresh _ _))
              (hoare_process_gpr_postLoop wgpr)
              (seq_skip_on
                (decCall_on_shaped hbal_rlp (ofString "bal") (.comb [.one, .one]) []
                  (callEntryOn_of_imp localsFree_guestInv (postLoopBase_guestInv (need64 := false)) _ _)
                  (resumeOn_build_bal_rlp_shaped wbal)
                  (TerminatingProgBoundedOn.seq_hoare
                    (TerminatingProgBoundedOn.call_on hvbal none _
                      (callEntryOn_of_imp localsFree_guestInv postLoopWithBal_guestInv _ _))
                    (hoare_validate_bal_gas_limit_postLoop hro_vbal)
                    (seq_skip_on
                      (TerminatingProgBoundedOn.decCall_on hal (ofString "root") .one [.const 32#64]
                        (callEntryOn_of_imp localsFree_guestInv postLoopWithBal_guestInv _ _)
                        (resumeOn_alloc_postLoopOut "root" 32 (by omega) (by decide)
                          (fun n hn => by
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                            rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
                          wal rtal)
                        (TerminatingProgBoundedOn.seq_hoare_trans
                          (TerminatingProgBoundedOn.call_on hcsr none _
                            (callEntryOn_of_imp localsFree_worldOK (postLoopWithOut_worldOK (outName := "root") (sz := 32)) _ _))
                          (hoare_compute_state_root_postLoop wcsr)
                          (seq_skip_on
                            (TerminatingProgBoundedOn.decCall_on hal (ofString "txroot") .one [.const 32#64]
                              (callEntryOn_of_imp localsFree_guestInv postLoopWithBal_guestInv _ _)
                              (resumeOn_alloc_postLoopOut "txroot" 32 (by omega) (by decide)
                                (fun n hn => by
                                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                                  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
                                wal rtal)
                              (TerminatingProgBoundedOn.seq_hoare_trans
                                (TerminatingProgBoundedOn.call_on hbmi none _ callEntryOn_build_mpt_indexed_txs)
                                (hoare_build_mpt_indexed_postLoop "txroot" _ _ wbmi)
                                (TerminatingProgBoundedOn.decCall_on hal (ofString "rroot") .one [.const 32#64]
                                  (callEntryOn_of_imp localsFree_guestInv postLoopWithBal_guestInv _ _)
                                  (resumeOn_alloc_postLoopOut "rroot" 32 (by omega) (by decide)
                                    (fun n hn => by
                                      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                                      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
                                    wal rtal)
                                  (TerminatingProgBoundedOn.seq_hoare_trans
                                    (TerminatingProgBoundedOn.call_on hbmi none _ callEntryOn_build_mpt_indexed_rcs)
                                    (hoare_build_mpt_indexed_postLoop "rroot" _ _ wbmi)
                                    (TerminatingProgBoundedOn.decCall_on hal (ofString "bloom") .one [.const 256#64]
                                      (callEntryOn_of_imp localsFree_guestInv postLoopWithBal_guestInv _ _)
                                      (resumeOn_alloc_postLoopOut "bloom" 256 (by omega) (by decide)
                                        (fun n hn => by
                                          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                                          rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
                                        wal rtal)
                                      (TerminatingProgBoundedOn.seq_hoare_trans
                                        (TerminatingProgBoundedOn.call_on hlb none _
                                          (callEntryOn_of_imp localsFree_guestInv (postLoopWithOut_guestInv (outName := "bloom") (sz := 256)) _ _))
                                        (hoare_logs_bloom_postLoop wlb)
                                        (TerminatingProgBoundedOn.decCall_on hal (ofString "wroot") .one [.const 32#64]
                                          (callEntryOn_of_imp localsFree_guestInv postBloom_guestInv _ _)
                                          (resumeOn_alloc_postBloomWroot wal rtal)
                                          (TerminatingProgBoundedOn.seq_hoare_trans
                                            (TerminatingProgBoundedOn.call_on hbmi none _ callEntryOn_build_mpt_indexed_wds)
                                            (hoare_guestInv_of_imp postBloomWithWroot_guestInv _)
                                            htail_gi)))))))))))))))))))
  intro F s hc hP
  exact (hbody s hc hP).weaken (by unfold kExecBlockPostLoop; omega)

private def PreAllocBo : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872

private theorem preAllocBo_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PreAllocBo s) : WorldOK s := by
  obtain ⟨_, _, _, _, _, _, hc, _⟩ := h
  exact blockContext_worldOK hc

private theorem preAllocBo_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PreAllocBo s) : GuestInv s :=
  worldOK_guestInv s (preAllocBo_worldOK s h)

private def PreMemzeroBo : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun {F} s =>
  ∃ w_si w_hdr w_pl w_ntx w_bo : BitVec 64, ∃ s0 bpost : PanSemStateFiniteExact 64 F,
  ∃ S Nd : List Nat,
    BlockContext s0 S Nd w_si.toNat w_hdr.toNat ∧
    ArenaReady bpost ∧
    AllocatorGrows s0 bpost ∧
    FreshBlock s0 bpost w_bo.toNat 88 ∧
    bpost.memory = s0.memory ∧
    bpost.be = s0.be ∧
    (∀ k : MlS, k ≠ ofString "heap_ptr" → s0.globals.lookup k = bpost.globals.lookup k) ∧
    s = { setGlobalHOLFinite (ofString "bo") (.val (.word w_bo)) bpost with
      locals := s.locals, clock := s.clock } ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    w_pl.toNat = memW s0 w_si.toNat ∧
    w_ntx.toNat = memW s0 (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872

private theorem preMemzeroBo_arenaReady {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PreMemzeroBo s) : ArenaReady s := by
  obtain ⟨_, _, _, _, w_bo, _, bpost, _, _, _, hAb, _, _, _, _, _, hs_eq, _⟩ := h
  rw [hs_eq]
  exact localsFree_arenaReady _ _ _
    (arenaReady_setGlobal_ne (by decide) (by decide) (by decide) hAb)

private theorem preMemzeroBo_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : PreMemzeroBo s) : GuestInv s :=
  (preMemzeroBo_arenaReady s h).1

private theorem hoare_call_global_bo_alloc
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    Hoare PreAllocBo
      (.call (some (some (.global, ofString "bo"), none)) (ofString "alloc") [.const 88#64])
      (fun r t => r = none → PreMemzeroBo t) := by
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (some (.global, ofString "bo"), none)) (ofString "alloc") [.const 88#64]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, S, Nd, hc, hsi, hhdr, hpl, hntx, hpl_eq, hntx_eq, hntx_le⟩ := hP
  rw [evaluateHOLFiniteState_call] at hcall
  rcases hargs : evalListHOLFinite state
      (h := fun a => Classical.propDecidable (state.memaddrs a)) [.const 88#64] with _ | values
  · rw [hargs] at hcall; simp at hcall
  · rw [hargs] at hcall; dsimp only at hcall
    rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "alloc") values with _ | ⟨body, callee, ret⟩
    · rw [hl] at hcall; simp at hcall
    · rw [hl] at hcall; dsimp only at hcall
      by_cases hz : state.clock = 0
      · rw [if_pos hz] at hcall; simp at hcall
      · rw [if_neg hz] at hcall
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, bpost⟩
        rw [hrun] at hcall
        cases bres with
        | none => simp at hcall
        | some br =>
          cases br with
          | returned v =>
            dsimp only at hcall
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret = true
            · rw [if_pos hsh] at hcall
              by_cases hv : isValidValueHOLExact state.toExact .global (ofString "bo") v = true
              · rw [if_pos hv] at hcall
                obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
                have hpc := callee_param_one_exp state (ofString "alloc") (ofString "n") .one _ _
                  (by rw [hcode]; exact lookup_alloc) (.const 88#64) (.val (.word 88#64))
                  values body callee ret rfl hargs hl
                have hn_loc : locN (callEntryStateHOLFinite state callee) "n" = 88 := by
                  simp [locN, callEntryStateHOLFinite, hpc.2]
                have hstep := FunSpec.at_lookup wal state hcode values body callee ret hl
                  (localsFree_worldOK state callee (state.clock - 1) (blockContext_worldOK hc))
                  (by rw [hrun]; simp)
                rw [hrun] at hstep; dsimp only at hstep
                have hws := hstep (Or.inl ⟨v, rfl⟩)
                have hrt := FunSpec.at_lookup rtal state hcode values body callee ret hl
                  (localsFree_arenaReady state callee (state.clock - 1) hc.arena)
                  (by rw [hrun]; simp)
                rw [hrun] at hrt; dsimp only at hrt
                obtain ⟨w_bo, rfl, hAb, hag_ce, hfb_ce⟩ := hrt v rfl
                rw [hn_loc] at hfb_ce
                have hmbe := alloc_call_mem_be_eq hcode hc.arena hl hrun
                have hag : AllocatorGrows state bpost := hag_ce
                have hfb : FreshBlock state bpost w_bo.toNat 88 := hfb_ce
                have hg_b : ∀ k : MlS, k ≠ ofString "heap_ptr" →
                    state.globals.lookup k = bpost.globals.lookup k :=
                  fun k hk => hws.2.2.1 k (by simpa using hk)
                have hcpost_eq : cpost = { setGlobalHOLFinite (ofString "bo") (.val (.word w_bo)) bpost with
                    locals := cpost.locals, clock := cpost.clock } := by
                  rw [← hpost_eq]; rfl
                have hcpost_loc : cpost.locals = state.locals := by
                  rw [← hpost_eq]; rfl
                exact ⟨w_si, w_hdr, w_pl, w_ntx, w_bo, state, bpost, S, Nd, hc, hAb, hag, hfb,
                  hmbe.1, hmbe.2, hg_b, hcpost_eq,
                  by rw [hcpost_loc]; exact hsi,
                  by rw [hcpost_loc]; exact hhdr,
                  by rw [hcpost_loc]; exact hpl,
                  by rw [hcpost_loc]; exact hntx,
                  hpl_eq, hntx_eq, hntx_le⟩
              · rw [if_neg hv] at hcall; simp at hcall
            · rw [if_neg hsh] at hcall; simp at hcall
          | _ => simp [emptyLocalsHOLFinite] at hcall

private def BoZeroState : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    (∀ off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)

private theorem boZeroState_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : BoZeroState s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, hc, _⟩ := h
  exact hc.arena.1

private theorem hoare_call_memzero_bo
    (wwmz : WritesWithin (fun s => [(locN s "dst", locN s "n")]) [] (ofString "memzero"))
    (zfmz : ZeroFills (ofString "memzero")) :
    Hoare PreMemzeroBo
      (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "bo"), .const 88#64])
      (fun r t => r = none → BoZeroState t) := by
  refine ⟨fun {F} state hcode hP _ hr => ?_⟩
  rcases hcall : evaluateHOLFiniteState state
      (.call (some (none, none)) (ofString "memzero")
        [.var .global (ofString "bo"), .const 88#64]) with ⟨cres, cpost⟩
  have hr' : cres = none := by rw [hcall] at hr; exact hr
  subst hr'
  have hAs := preMemzeroBo_arenaReady state hP
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_bo, s0, bpost, S, Nd, hc0, hAb, hag, hfb,
    hmem_b, hbe_b, hg_b, hs_eq, hsi, hhdr, hpl, hntx, hpl_eq0, hntx_eq0, hntx_le⟩ := hP
  have hbo_lu : state.globals.lookup (ofString "bo") = some (.val (.word w_bo)) := by
    rw [hs_eq]; simp [setGlobalHOLFinite, HolFiniteMapExact.update, FUPDATE]
  rw [evaluateHOLFiniteState_call] at hcall
  have hargs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .global (ofString "bo"), .const 88#64] =
      some [.val (.word w_bo), .val (.word 88#64)] := by
    rw [evalListHOLFinite_eq_toExact]; simp [evalListHOLExact, evalHOLExact, hbo_lu]
  rw [hargs] at hcall; dsimp only at hcall
  rcases hl : lookupCodeHOLFinite state.code.lookup (ofString "memzero")
      [.val (.word w_bo), .val (.word 88#64)] with _ | ⟨body, callee, ret⟩
  · rw [hl] at hcall; simp at hcall
  · rw [hl] at hcall; dsimp only at hcall
    split_ifs at hcall with hz
    · simp at hcall
    · have hmeta := (evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state callee) body).2.2.2
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite state callee) body with ⟨bres, s2⟩
      rw [hrun] at hcall hmeta
      dsimp only at hmeta
      cases bres with
      | none => simp at hcall
      | some br =>
        cases br with
        | returned v =>
          dsimp only at hcall
          split_ifs at hcall with hsh
          · obtain ⟨_, hpost_eq⟩ := Prod.mk.inj hcall
            have hpc := callee_param_two state (ofString "memzero") (ofString "dst") (ofString "n")
              .one .one _ _ (by rw [hcode]; exact R13PayloadStateInit.lookup_memzero_fn)
              (.var .global (ofString "bo")) (.const 88#64)
              (.val (.word w_bo)) (.val (.word 88#64))
              [.val (.word w_bo), .val (.word 88#64)] body callee ret
              (by simpa [evalAt, evalHOLExact] using hbo_lu) rfl hargs hl
            have hdst : locN (callEntryStateHOLFinite state callee) "dst" = w_bo.toNat := by
              simp [locN, callEntryStateHOLFinite, hpc.2.1]
            have hn : locN (callEntryStateHOLFinite state callee) "n" = 88 := by
              simp [locN, callEntryStateHOLFinite, hpc.2.2]
            have hww := FunSpec.at_lookup wwmz state hcode _ body callee ret hl
              (localsFree_arenaReady state callee (state.clock - 1) hAs)
              (by rw [hrun]; simp)
            rw [hrun] at hww; dsimp only at hww
            obtain ⟨hA2, hhp2, hsc2, hfr2, hg2⟩ := hww (Or.inl ⟨v, rfl⟩)
            have hzf0 := FunSpec.at_lookup zfmz state hcode _ body callee ret hl
              (localsFree_arenaReady state callee (state.clock - 1) hAs)
              (by rw [hrun]; simp)
            rw [hrun] at hzf0; dsimp only at hzf0
            have hzf := hzf0 v rfl
            rw [hdst, hn] at hfr2 hzf
            have hhp_ce : globN (callEntryStateHOLFinite state callee) "heap_ptr" = globN bpost "heap_ptr" := by
              change globN state "heap_ptr" = globN bpost "heap_ptr"
              rw [hs_eq]
              exact globN_setGlobal_ne bpost (ofString "bo") (.val (.word w_bo)) "heap_ptr" (by decide)
            have hfm_ce : globN (callEntryStateHOLFinite state callee) "frame_mem_ptr" = globN bpost "frame_mem_ptr" := by
              change globN state "frame_mem_ptr" = globN bpost "frame_mem_ptr"
              rw [hs_eq]
              exact globN_setGlobal_ne bpost (ofString "bo") (.val (.word w_bo)) "frame_mem_ptr" (by decide)
            have hsc_ce : globN (callEntryStateHOLFinite state callee) "scratch_ptr" = globN bpost "scratch_ptr" := by
              change globN state "scratch_ptr" = globN bpost "scratch_ptr"
              rw [hs_eq]
              exact globN_setGlobal_ne bpost (ofString "bo") (.val (.word w_bo)) "scratch_ptr" (by decide)
            rw [hhp_ce] at hhp2
            rw [hsc_ce] at hsc2
            rw [hhp_ce, hfm_ce, hsc_ce] at hfr2
            have hbe_2 : s2.be = bpost.be := by
              have hmeta_be := (PanRunBounded.evaluateHOLFiniteState_metadata
                (callEntryStateHOLFinite state callee) body).2.2.1
              rw [hrun] at hmeta_be; dsimp only at hmeta_be
              rw [hmeta_be]
              change state.be = bpost.be
              rw [hs_eq]; rfl
            have hg_2 : ∀ k : MlS,
                (setGlobalHOLFinite (ofString "bo") (.val (.word w_bo)) bpost).globals.lookup k =
                  s2.globals.lookup k := by
              intro k
              have hk := hg2 k (by simp)
              change state.globals.lookup k = s2.globals.lookup k at hk
              rw [hs_eq] at hk
              exact hk
            have hfr_bpost : FrameOutside bpost s2
                ([(w_bo.toNat, 88)] ++ [(globN bpost "frame_mem_ptr",
                  globN bpost "scratch_ptr" - globN bpost "frame_mem_ptr")])
                (globN bpost "heap_ptr", heapLimit - globN bpost "heap_ptr") := by
              intro a ha hnf
              have h1 := hfr2 a ha hnf
              change s2.memory a = state.memory a at h1
              rw [hs_eq] at h1
              exact h1
            obtain ⟨hc2, hbo_s2, hbo_nz2, hz_s2⟩ :=
              blockContext_alloc_bo_memzero hc0 hAb hag hfb hmem_b hbe_b hg_b
                hA2 hbe_2 hhp2 hsc2 hg_2 hfr_bpost hzf
            have hcin0 : ∀ c ∈ inputRegions s0 w_si.toNat w_hdr.toNat,
                c.1 % 8 = 0 ∧ Inside c sourceBase (globN s0 "heap_ptr") ∧ WordsOK s0 c :=
              fun c hm => ⟨(hc0.regions c hm).1, (hc0.regions c hm).2.2.1, (hc0.regions c hm).2.2.2.1⟩
            have hu_reg0 : ∀ c ∈ inputRegions s0 w_si.toNat w_hdr.toNat, IvlUnhit s0 s2 c := by
              intro c hm
              obtain ⟨hc8, _, hcin, _, _⟩ := hc0.regions c hm
              have hu_b : IvlUnhit bpost s2 c := ivlUnhit_of_memzero_frame hAb hfb.1 (by decide) hc8
                ⟨hcin.1, hcin.2.trans hag.1⟩ (disj_fresh_tracked hfb hc0.regions c hm) hfr_bpost
              intro a ha8 hhit
              rw [hu_b a ha8 hhit, hmem_b]
            have hsi0_eq : memW s2 w_si.toNat = memW s0 w_si.toNat := by
              simpa only [Nat.add_zero] using
                inputRegions_word_eq hc0.arena hcin0 hu_reg0 (c := (w_si.toNat, 96))
                  (by simp [inputRegions]) (off := 0) (by omega) (by omega)
            have hpl40_eq : memW s2 (memW s0 w_si.toNat + 40) = memW s0 (memW s0 w_si.toNat + 40) :=
              inputRegions_word_eq hc0.arena hcin0 hu_reg0 (c := (memW s0 w_si.toNat, 136))
                (by simp [inputRegions]) (off := 40) (by omega) (by omega)
            rw [← hpost_eq]
            refine ⟨w_si, w_hdr, w_pl, w_ntx, S, Nd,
              (blockContext_with_locals s2 state.locals s2.clock S Nd w_si.toNat w_hdr.toNat).2 hc2,
              hsi, hhdr, hpl, hntx,
              by change w_pl.toNat = memW s2 w_si.toNat; rw [hsi0_eq]; exact hpl_eq0,
              by change w_ntx.toNat = memW s2 (w_pl.toNat + 40); rw [hpl_eq0, hpl40_eq, ← hpl_eq0]; exact hntx_eq0,
              hntx_le, hbo_nz2, ?_⟩
            intro off hoff
            change memW s2 (globN s2 "bo" + off) = 0
            rw [hbo_s2]
            exact hz_s2 off (by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢
              rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
          · simp at hcall
        | _ => simp [emptyLocalsHOLFinite] at hcall

private theorem evalAt_add_global_bo_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {S Nd : List Nat} (hA : ArenaOK s) (hW : WorldTypedWith s S Nd) (hbo_nz : globN s "bo" ≠ 0)
    {off : Nat} (hoff_lt : off + 8 ≤ 88) {x : BitVec 64}
    (hx : evalAt s (.op .add [.var .global (ofString "bo"), .const (BitVec.ofNat 64 off)]) =
      some (.val (.word x))) :
    x.toNat = globN s "bo" + off := by
  obtain ⟨w1, w2, he1, he2, rfl⟩ := evalAt_add2_words hx
  have hbo_lu : s.globals.lookup (ofString "bo") = some (.val (.word w1)) := by
    simpa [evalAt, evalHOLExact] using he1
  have hw1_eq : w1.toNat = globN s "bo" := by simp [globN, hbo_lu]
  have hw2_eq : w2 = BitVec.ofNat 64 off := by
    simpa [evalAt, evalHOLExact] using he2.symm
  subst hw2_eq
  have hbo_hi := (bo_allocated_wordsOK hA hW hbo_nz).2.2.2
  have hoff_lt64 : off < 2 ^ 64 := by omega
  have hw2_nat : (BitVec.ofNat 64 off).toNat = off := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hoff_lt64]
  rw [BitVec.toNat_add, hw1_eq, hw2_nat, Nat.mod_eq_of_lt (by omega)]

private theorem evalAt_alloc_ntx_size {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w_ntx : BitVec 64} (hntx : s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)))
    (hwrap : 16 * w_ntx.toNat + 16 < 2 ^ 64) :
    ∃ w_sz : BitVec 64,
      evalAt s (.op .add [.panop .mul [.var .local (ofString "ntx"), .const 16#64], .const 16#64]) =
        some (.val (.word w_sz)) ∧
      w_sz.toNat = 16 * w_ntx.toNat + 16 := by
  have hev : evalAt s (.op .add [.panop .mul [.var .local (ofString "ntx"), .const 16#64], .const 16#64]) =
      some (.val (.word (w_ntx * 16#64 + 16#64))) := by
    simp only [evalAt, PanSemStateFiniteExact.toExact, evalHOLExact, evalListHOLExact, hntx,
      List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr,
      valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq]
    have hz : (16#64 : BitVec 64) + 0 = 16#64 := BitVec.add_zero _
    rw [hz]
  refine ⟨w_ntx * 16#64 + 16#64, hev, ?_⟩
  have h16 : (16#64 : BitVec 64).toNat = 16 := rfl
  have hmul : (w_ntx * 16#64).toNat = 16 * w_ntx.toNat := by
    rw [BitVec.toNat_mul, h16, Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_add, hmul, h16, Nat.mod_eq_of_lt hwrap]

private def BoAfterTxsAlloc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat
      [(w_txs.toNat, 16), (w_txs.toNat + 16, 16 * w_ntx.toNat)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    (∀ off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)

private theorem resumeOn_alloc_txs
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn BoZeroState BoAfterTxsAlloc (ofString "txs") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "ntx"), .const 16#64], .const 16#64]] := by
  intro F s values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, S, Nd, hc, hsi, hhdr, hpl, hntx,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, hz⟩ := hP
  have hwrap : 16 * w_ntx.toNat + 16 < 2 ^ 64 := by
    rw [hntx_eq, hpl_eq]; exact hc.ntx_wrap
  obtain ⟨w_sz, hev_sz, hsz_eq⟩ := evalAt_alloc_ntx_size hntx hwrap
  have hpc := callee_param_one_exp s (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc) _ (.val (.word w_sz)) values body callee ret hev_sz hargs hl
  have hn_loc : locN (callEntryStateHOLFinite s callee) "n" = 16 * w_ntx.toNat + 16 := by
    simp [locN, callEntryStateHOLFinite, hpc.2, hsz_eq]
  have hround : ((16 * w_ntx.toNat + 16) + 7) / 8 * 8 = 16 * w_ntx.toNat + 16 := by omega
  have hstep := FunSpec.at_lookup wal s hcode values body callee ret hl
    (localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc)) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal s hcode values body callee ret hl
    (localsFree_arenaReady s callee (s.clock - 1) hc.arena) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_txs, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hmbe := alloc_call_mem_be_eq hcode hc.arena hl hrun
  have hmemW_eq : ∀ addr : Nat, memW post addr = memW s addr := by
    intro addr; unfold memW; rw [hmbe.1]
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (hws.2.2.1 _ (by decide : ofString "bo" ∉ ["heap_ptr"].map ofString))
  have hc_ce : BlockContext (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  have hws' : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ p => [(p, ((16 * w_ntx.toNat + 16) + 7) / 8 * 8)]))
      (callEntryStateHOLFinite s callee) (some (.returned (.val (.word w_txs)))) post := by
    refine ⟨hws.1, hws.2.1, hws.2.2.1, hws.2.2.2.1, ?_⟩
    intro S₀ Nd₀ hWT₀ hDisj₀
    obtain ⟨S', Nd', hsub, hWT', hOg', hFo', hQ'⟩ := hws.2.2.2.2 S₀ Nd₀ hWT₀ hDisj₀
    refine ⟨S', Nd', hsub, hWT', hOg', hFo', ?_⟩
    intro v hv
    obtain ⟨w', hw', hd'⟩ := hQ' v hv
    exact ⟨w', hw', by dsimp only at hd' ⊢; rwa [hn_loc] at hd'⟩
  obtain ⟨S', Nd', hc_post, htd_post, htxs_nz, _, _⟩ :=
    trackedDisjIn_alloc_result hc_ce trackedDisjIn_nil hfb hws'
  rw [hround] at htd_post
  have htd_parts := trackedDisjIn_sub_parts hc_post.arena htd_post
  rw [List.nil_append] at htd_parts
  have hin_txs : Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN post "heap_ptr") :=
    ⟨hc.arena.2.1.trans hfb.2.1.1, by have h2 := hfb.2.1.2; dsimp only at h2 ⊢; omega⟩
  set resumed := setVarHOLFinite (ofString "txs") (.val (.word w_txs)) { post with locals := s.locals }
  refine ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, S', Nd',
    (blockContext_with_locals post _ post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    ⟨(trackedBlocks_with_locals post _ post.clock S' Nd' _).2 htd_parts.1,
      htd_parts.2.1, htd_parts.2.2.1, htd_parts.2.2.2⟩,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "txs" ≠ ofString "si" from by decide, hsi],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "txs" ≠ ofString "hdr" from by decide, hhdr],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "txs" ≠ ofString "pl" from by decide, hpl],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "txs" ≠ ofString "ntx" from by decide, hntx],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by change w_pl.toNat = memW post w_si.toNat; rw [hmemW_eq]; exact hpl_eq,
    by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hmemW_eq]; exact hntx_eq,
    hntx_le,
    by change globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
    htxs_nz, hin_txs,
    fun off hoff => by change memW post (globN post "bo" + off) = 0; rw [hbo_eq, hmemW_eq]; exact hz off hoff⟩

private def BoAfterStore24 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat [(w_txs.toNat + 16, 16 * w_ntx.toNat)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    (∀ off ∈ ([32, 40, 56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)

private theorem boAfterStore24_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : BoAfterStore24 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, hc, _⟩ := h; exact hc.arena.1

private theorem hoare_store_bo_24 :
    Hoare BoAfterTxsAlloc
      (.store (.op .add [.var .global (ofString "bo"), .const 24#64]) (.var .local (ofString "txs")))
      (fun r t => r = none → BoAfterStore24 t) := by
  apply Hoare.store_fall
  intro F s x v mem' hP hx hv hst
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, S, Nd, hc, htd, hsi, hhdr, hpl, hntx, htxs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hin_txs, hz⟩ := hP
  have hv_eq : v = .val (.word w_txs) := by
    simpa [evalAt, evalHOLExact, htxs] using hv.symm
  subst hv_eq
  obtain ⟨_, hsame, hframe⟩ := panMemStoresHOL_word_spec (s := s) (by simpa [flattenHOL] using hst)
  have hx_eq := evalAt_add_global_bo_const hc.arena.2 hc.world hbo_nz (off := 24) (by decide) hx
  obtain ⟨hc_p, htd_p, hbo_nz_p, h24_p, hz_p⟩ :=
    bo_store_24 hc htd hbo_nz htxs_nz hz hx_eq hsame hframe
  set post := { s with memory := mem' }
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hbo_mem_ow := bo_in_worldOwned (S := S) (Nd := Nd) hbo_nz
  have hx_in_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hu_reg : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat, IvlUnhit s post c := by
    intro c hcm
    obtain ⟨hc8, _, _, _, hd_ow⟩ := hc.regions c hcm
    exact ivlUnhit_of_single_cell_disj (fun _ => hc8) hframe
      (disj_of_inside_left hx_in_bo (hd_ow _ hbo_mem_ow).flip).flip
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, S, Nd, hc_p, htd_p, hsi, hhdr, hpl, hntx, htxs,
    by rw [hsi0_eq]; exact hpl_eq,
    by rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le, hbo_nz_p, htxs_nz, h24_p, hin_txs, hz_p⟩

private def BoAfterRcsAlloc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (w_rcs.toNat, 16), (w_rcs.toNat + 16, 16 * w_ntx.toNat)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    (∀ off ∈ ([32, 40, 56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)

private theorem resumeOn_alloc_rcs
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn BoAfterStore24 BoAfterRcsAlloc (ofString "rcs") (ofString "alloc")
      [.op .add [.panop .mul [.var .local (ofString "ntx"), .const 16#64], .const 16#64]] := by
  intro F s values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, S, Nd, hc, htd, hsi, hhdr, hpl, hntx, htxs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, h24, hin_txs, hz⟩ := hP
  have hwrap : 16 * w_ntx.toNat + 16 < 2 ^ 64 := by
    rw [hntx_eq, hpl_eq]; exact hc.ntx_wrap
  obtain ⟨w_sz, hev_sz, hsz_eq⟩ := evalAt_alloc_ntx_size hntx hwrap
  have hpc := callee_param_one_exp s (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc) _ (.val (.word w_sz)) values body callee ret hev_sz hargs hl
  have hn_loc : locN (callEntryStateHOLFinite s callee) "n" = 16 * w_ntx.toNat + 16 := by
    simp [locN, callEntryStateHOLFinite, hpc.2, hsz_eq]
  have hround : ((16 * w_ntx.toNat + 16) + 7) / 8 * 8 = 16 * w_ntx.toNat + 16 := by omega
  have hstep := FunSpec.at_lookup wal s hcode values body callee ret hl
    (localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc)) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal s hcode values body callee ret hl
    (localsFree_arenaReady s callee (s.clock - 1) hc.arena) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_rcs, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hmbe := alloc_call_mem_be_eq hcode hc.arena hl hrun
  have hmemW_eq : ∀ addr : Nat, memW post addr = memW s addr := by
    intro addr; unfold memW; rw [hmbe.1]
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (hws.2.2.1 _ (by decide : ofString "bo" ∉ ["heap_ptr"].map ofString))
  have hc_ce : BlockContext (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  have htd_ce : TrackedDisjIn (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat
      [(w_txs.toNat + 16, 16 * w_ntx.toNat)] :=
    ⟨(trackedBlocks_with_locals s callee (s.clock - 1) S Nd _).2 htd.1, htd.2.1, htd.2.2.1, htd.2.2.2⟩
  have hws' : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ p => [(p, ((16 * w_ntx.toNat + 16) + 7) / 8 * 8)]))
      (callEntryStateHOLFinite s callee) (some (.returned (.val (.word w_rcs)))) post := by
    refine ⟨hws.1, hws.2.1, hws.2.2.1, hws.2.2.2.1, ?_⟩
    intro S₀ Nd₀ hWT₀ hDisj₀
    obtain ⟨S', Nd', hsub, hWT', hOg', hFo', hQ'⟩ := hws.2.2.2.2 S₀ Nd₀ hWT₀ hDisj₀
    refine ⟨S', Nd', hsub, hWT', hOg', hFo', ?_⟩
    intro v hv
    obtain ⟨w', hw', hd'⟩ := hQ' v hv
    exact ⟨w', hw', by dsimp only at hd' ⊢; rwa [hn_loc] at hd'⟩
  obtain ⟨S', Nd', hc_post, htd_post, hrcs_nz, _, _⟩ :=
    trackedDisjIn_alloc_result hc_ce htd_ce hfb hws'
  rw [hround] at htd_post
  have htd_parts := trackedDisjIn_sub_parts hc_post.arena htd_post
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
  have hin_rcs : Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN post "heap_ptr") :=
    ⟨hc.arena.2.1.trans hfb.2.1.1, by have h2 := hfb.2.1.2; dsimp only at h2 ⊢; omega⟩
  have h24_post : memW post (globN post "bo" + 24) = w_txs.toNat := by
    rw [hbo_eq, hmemW_eq]; exact h24
  rw [← h24_post] at htd_parts
  set resumed := setVarHOLFinite (ofString "rcs") (.val (.word w_rcs)) { post with locals := s.locals }
  refine ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S', Nd',
    (blockContext_with_locals post _ post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    ⟨(trackedBlocks_with_locals post _ post.clock S' Nd' _).2 htd_parts.1,
      htd_parts.2.1, htd_parts.2.2.1, htd_parts.2.2.2⟩,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rcs" ≠ ofString "si" from by decide, hsi],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rcs" ≠ ofString "hdr" from by decide, hhdr],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rcs" ≠ ofString "pl" from by decide, hpl],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rcs" ≠ ofString "ntx" from by decide, hntx],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rcs" ≠ ofString "txs" from by decide, htxs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by change w_pl.toNat = memW post w_si.toNat; rw [hmemW_eq]; exact hpl_eq,
    by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hmemW_eq]; exact hntx_eq,
    hntx_le,
    by change globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
    htxs_nz, hrcs_nz, h24_post,
    ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩, hin_rcs,
    fun off hoff => by change memW post (globN post "bo" + off) = 0; rw [hbo_eq, hmemW_eq]; exact hz off hoff⟩

private def BoAfterStore32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w_ntx.toNat)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    (∀ off ∈ ([40, 56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)

private theorem boAfterStore32_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : BoAfterStore32 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := h; exact hc.arena.1

private theorem hoare_store_bo_32 :
    Hoare BoAfterRcsAlloc
      (.store (.op .add [.var .global (ofString "bo"), .const 32#64]) (.var .local (ofString "rcs")))
      (fun r t => r = none → BoAfterStore32 t) := by
  apply Hoare.store_fall
  intro F s x v mem' hP hx hv hst
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, htd, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, hin_txs, hin_rcs, hz⟩ := hP
  have hv_eq : v = .val (.word w_rcs) := by
    simpa [evalAt, evalHOLExact, hrcs] using hv.symm
  subst hv_eq
  obtain ⟨_, hsame, hframe⟩ := panMemStoresHOL_word_spec (s := s) (by simpa [flattenHOL] using hst)
  have hx_eq := evalAt_add_global_bo_const hc.arena.2 hc.world hbo_nz (off := 32) (by decide) hx
  obtain ⟨hc_p, htd_p, hbo_nz_p, _, h32_p, hz_p⟩ :=
    bo_store_32 hc htd hbo_nz (by rw [h24]; exact htxs_nz) hrcs_nz hz hx_eq hsame hframe
  set post := { s with memory := mem' }
  have h24_p : memW post (globN post "bo" + 24) = w_txs.toNat := by
    rw [show globN post "bo" = globN s "bo" from rfl,
      memW_bo_store_ne hc.arena.2 hc.world hbo_nz (by decide) (by decide) hx_eq hframe, h24]
  have htd_p' : TrackedDisjIn post S Nd w_si.toNat w_hdr.toNat
      [(memW post (globN post "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW post (globN post "bo" + 32) + 16, 16 * w_ntx.toNat)] := by
    rw [h32_p]; exact htd_p
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hbo_mem_ow := bo_in_worldOwned (S := S) (Nd := Nd) hbo_nz
  have hx_in_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hu_reg : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat, IvlUnhit s post c := by
    intro c hcm
    obtain ⟨hc8, _, _, _, hd_ow⟩ := hc.regions c hcm
    exact ivlUnhit_of_single_cell_disj (fun _ => hc8) hframe
      (disj_of_inside_left hx_in_bo (hd_ow _ hbo_mem_ow).flip).flip
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc_p, htd_p', hsi, hhdr, hpl, hntx, htxs, hrcs,
    by rw [hsi0_eq]; exact hpl_eq,
    by rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le, hbo_nz_p, htxs_nz, hrcs_nz, h24_p, h32_p, hin_txs, hin_rcs, hz_p⟩

private def BoAfterLogsNew : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs w_logs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w_ntx.toNat),
       (w_logs.toNat, 24), (memW s w_logs.toNat, 128)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    s.locals.lookup (ofString "logs") = some (.val (.word w_logs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    w_logs.toNat ≠ 0 ∧
    memW s w_logs.toNat ≠ 0 ∧
    memW s (w_logs.toNat + 8) = 0 ∧
    memW s (w_logs.toNat + 16) = 16 ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    (∀ off ∈ ([40, 56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)

private theorem resumeOn_lst_new_logs
    (wlst : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
        (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")])) (ofString "lst_new"))
    (rtlst : Returns ArenaReady (fun s post l =>
        locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
          FreshBlock s post l 24 ∧ FreshBlock s post (memW post l) (locN s "esz" * locN s "cap") ∧
          Disj (l, 24) (memW post l, locN s "esz" * locN s "cap") ∧
          memW post (l + 8) = 0 ∧ memW post (l + 16) = locN s "cap")
      (ofString "lst_new")) :
    DecCallResumeOn BoAfterStore32 BoAfterLogsNew (ofString "logs") (ofString "lst_new")
      [.const 8#64, .const 16#64] := by
  intro F s values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, htd, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, hin_txs, hin_rcs, hz⟩ := hP
  have hpc := callee_param_two s (ofString "lst_new") (ofString "esz") (ofString "cap") .one .one _ _
    (by rw [hcode]; exact lookup_lst_new_fn) _ _ (.val (.word 8#64)) (.val (.word 16#64))
    values body callee ret rfl rfl hargs hl
  have hesz_loc : locN (callEntryStateHOLFinite s callee) "esz" = 8 := by
    simp [locN, callEntryStateHOLFinite, hpc.2.1]
  have hcap_loc : locN (callEntryStateHOLFinite s callee) "cap" = 16 := by
    simp [locN, callEntryStateHOLFinite, hpc.2.2]
  have hstep := FunSpec.at_lookup wlst s hcode values body callee ret hl
    (localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc)) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtlst s hcode values body callee ret hl
    (localsFree_arenaReady s callee (s.clock - 1) hc.arena) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_logs, rfl, _, _, hfb_imp⟩ := hrt value rfl
  have hfb_all := hfb_imp (by rw [hesz_loc, hcap_loc]; decide) (by rw [hcap_loc]; decide)
  rw [hesz_loc, hcap_loc] at hfb_all
  have hmul128 : 8 * 16 = 128 := rfl
  rw [hmul128] at hfb_all
  obtain ⟨hhead, hdata, hd_hd, hlen, hcap⟩ := hfb_all
  have hc_ce : BlockContext (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  have htd_ce : TrackedDisjIn (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w_ntx.toNat)] :=
    ⟨(trackedBlocks_with_locals s callee (s.clock - 1) S Nd _).2 htd.1, htd.2.1, htd.2.2.1, htd.2.2.2⟩
  have hws' : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ post p => [(p, 24), (memW post p, 128)]))
      (callEntryStateHOLFinite s callee) (some (.returned (.val (.word w_logs)))) post := by
    refine ⟨hws.1, hws.2.1, hws.2.2.1, hws.2.2.2.1, ?_⟩
    intro S₀ Nd₀ hWT₀ hDisj₀
    obtain ⟨S', Nd', hsub, hWT', hOg', hFo', hQ'⟩ := hws.2.2.2.2 S₀ Nd₀ hWT₀ hDisj₀
    refine ⟨S', Nd', hsub, hWT', hOg', hFo', ?_⟩
    intro v hv
    have hQ'' := hQ' (by dsimp only; rw [hesz_loc, hcap_loc]; decide) v hv
    obtain ⟨w', hw', hd'⟩ := hQ''
    exact ⟨w', hw', by dsimp only at hd' ⊢; rwa [hesz_loc, hcap_loc] at hd'⟩
  obtain ⟨S', Nd', hc_post, htd_post, _, hlogs_nz, hlogs0_nz, hu_reg, _⟩ :=
    trackedDisjIn_lst_new_result hc_ce htd_ce hhead hdata hd_hd hlen hcap hws'
  have hbo_slot : ∀ off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat),
      globN post "bo" = globN s "bo" ∧ memW post (globN post "bo" + off) = memW s (globN s "bo" + off) := by
    intro off hoff
    have hoff_keep : off ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    have hoff8 : off % 8 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hoff_lt : off + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact bo_slot_eq_of_worldStep (s := callEntryStateHOLFinite s callee)
      hc_ce.arena.2 hc_ce.world (by exact hbo_nz) hws'
      (by decide) (by simp) hoff_keep hoff8 hoff_lt (by intro _ hm; cases hm) (by intro _ hm; cases hm)
  have hbo_eq : globN post "bo" = globN s "bo" := (hbo_slot 24 (by simp)).1
  have h24_post : memW post (globN post "bo" + 24) = w_txs.toNat := by
    rw [(hbo_slot 24 (by simp)).2]; exact h24
  have h32_post : memW post (globN post "bo" + 32) = w_rcs.toNat := by
    rw [(hbo_slot 32 (by simp)).2]; exact h32
  have htd_post' : TrackedDisjIn post S' Nd' w_si.toNat w_hdr.toNat
      [(memW post (globN post "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW post (globN post "bo" + 32) + 16, 16 * w_ntx.toNat),
       (w_logs.toNat, 24), (memW post w_logs.toNat, 128)] := by
    rw [(hbo_slot 24 (by simp)).2, (hbo_slot 32 (by simp)).2]; exact htd_post
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
  set resumed := setVarHOLFinite (ofString "logs") (.val (.word w_logs)) { post with locals := s.locals }
  refine ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_logs, S', Nd',
    (blockContext_with_locals post _ post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    ⟨(trackedBlocks_with_locals post _ post.clock S' Nd' _).2 htd_post'.1,
      htd_post'.2.1, htd_post'.2.2.1, htd_post'.2.2.2⟩,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "logs" ≠ ofString "si" from by decide, hsi],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "logs" ≠ ofString "hdr" from by decide, hhdr],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "logs" ≠ ofString "pl" from by decide, hpl],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "logs" ≠ ofString "ntx" from by decide, hntx],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "logs" ≠ ofString "txs" from by decide, htxs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "logs" ≠ ofString "rcs" from by decide, hrcs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by change w_pl.toNat = memW post w_si.toNat; rw [hsi0_eq]; exact hpl_eq,
    by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le,
    by change globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
    htxs_nz, hrcs_nz, h24_post, h32_post,
    hlogs_nz, hlogs0_nz, hlen, hcap,
    ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩, ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩,
    fun off hoff => by
      change memW post (globN post "bo" + off) = 0
      have hoff' : off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢
        rcases hoff with rfl | rfl | rfl | rfl | rfl <;> simp
      rw [(hbo_slot off hoff').2]; exact hz off hoff⟩

private def BoAfterStore40 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w_ntx.toNat)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    (∀ off ∈ ([56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)

private theorem boAfterStore40_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : BoAfterStore40 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := h; exact hc.arena.1

private theorem hoare_store_bo_40 :
    Hoare BoAfterLogsNew
      (.store (.op .add [.var .global (ofString "bo"), .const 40#64]) (.var .local (ofString "logs")))
      (fun r t => r = none → BoAfterStore40 t) := by
  apply Hoare.store_fall
  intro F s x v mem' hP hx hv hst
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_logs, S, Nd, hc, htd,
    hsi, hhdr, hpl, hntx, htxs, hrcs, hlogs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32,
    hlogs_nz, hlogs0_nz, hlen, hcap, hin_txs, hin_rcs, hz⟩ := hP
  have hv_eq : v = .val (.word w_logs) := by
    simpa [evalAt, evalHOLExact, hlogs] using hv.symm
  subst hv_eq
  obtain ⟨_, hsame, hframe⟩ := panMemStoresHOL_word_spec (s := s) (by simpa [flattenHOL] using hst)
  have hx_eq := evalAt_add_global_bo_const hc.arena.2 hc.world hbo_nz (off := 40) (by decide) hx
  obtain ⟨hc_p, htd_p, hbo_nz_p, _, _, h40_p, hz_p⟩ :=
    bo_store_40 hc htd hbo_nz (by rw [h24]; exact htxs_nz) (by rw [h32]; exact hrcs_nz)
      hlogs_nz hlogs0_nz hlen hcap hz hx_eq hsame hframe
  set post := { s with memory := mem' }
  have h24_p : memW post (globN post "bo" + 24) = w_txs.toNat := by
    rw [show globN post "bo" = globN s "bo" from rfl,
      memW_bo_store_ne hc.arena.2 hc.world hbo_nz (by decide) (by decide) hx_eq hframe, h24]
  have h32_p : memW post (globN post "bo" + 32) = w_rcs.toNat := by
    rw [show globN post "bo" = globN s "bo" from rfl,
      memW_bo_store_ne hc.arena.2 hc.world hbo_nz (by decide) (by decide) hx_eq hframe, h32]
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hbo_mem_ow := bo_in_worldOwned (S := S) (Nd := Nd) hbo_nz
  have hx_in_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hu_reg : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat, IvlUnhit s post c := by
    intro c hcm
    obtain ⟨hc8, _, _, _, hd_ow⟩ := hc.regions c hcm
    exact ivlUnhit_of_single_cell_disj (fun _ => hc8) hframe
      (disj_of_inside_left hx_in_bo (hd_ow _ hbo_mem_ow).flip).flip
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc_p, htd_p, hsi, hhdr, hpl, hntx, htxs, hrcs,
    by rw [hsi0_eq]; exact hpl_eq,
    by rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le, hbo_nz_p, htxs_nz, hrcs_nz, h24_p, h32_p,
    by rw [h40_p]; exact hlogs_nz,
    hin_txs, hin_rcs, hz_p⟩

private def BoAfterReqsAlloc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs w_reqs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w_ntx.toNat),
       (w_reqs.toNat, 128)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    s.locals.lookup (ofString "reqs") = some (.val (.word w_reqs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧
    w_reqs.toNat ≠ 0 ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    (∀ off ∈ ([56, 64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)

private theorem resumeOn_alloc_reqs
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc")) :
    DecCallResumeOn BoAfterStore40 BoAfterReqsAlloc (ofString "reqs") (ofString "alloc")
      [.panop .mul [.const 8#64, .const 16#64]] := by
  intro F s values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, htd, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40_nz, hin_txs, hin_rcs, hz⟩ := hP
  have hev_128 : evalAt s (.panop .mul [.const 8#64, .const 16#64]) = some (.val (.word 128#64)) := rfl
  have hpc := callee_param_one_exp s (ofString "alloc") (ofString "n") .one _ _
    (by rw [hcode]; exact lookup_alloc) _ (.val (.word 128#64)) values body callee ret hev_128 hargs hl
  have hn_loc : locN (callEntryStateHOLFinite s callee) "n" = 128 := by
    simp [locN, callEntryStateHOLFinite, hpc.2]
  have hstep := FunSpec.at_lookup wal s hcode values body callee ret hl
    (localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc)) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtal s hcode values body callee ret hl
    (localsFree_arenaReady s callee (s.clock - 1) hc.arena) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_reqs, rfl, _, _, hfb⟩ := hrt value rfl
  rw [hn_loc] at hfb
  have hmbe := alloc_call_mem_be_eq hcode hc.arena hl hrun
  have hmemW_eq : ∀ addr : Nat, memW post addr = memW s addr := by
    intro addr; unfold memW; rw [hmbe.1]
  have hbo_eq : globN post "bo" = globN s "bo" :=
    globN_eq_of_lookup (hws.2.2.1 _ (by decide : ofString "bo" ∉ ["heap_ptr"].map ofString))
  have hc_ce : BlockContext (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  have htd_ce : TrackedDisjIn (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w_ntx.toNat)] :=
    ⟨(trackedBlocks_with_locals s callee (s.clock - 1) S Nd _).2 htd.1, htd.2.1, htd.2.2.1, htd.2.2.2⟩
  have hws' : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ _ p => [(p, (128 + 7) / 8 * 8)]))
      (callEntryStateHOLFinite s callee) (some (.returned (.val (.word w_reqs)))) post := by
    refine ⟨hws.1, hws.2.1, hws.2.2.1, hws.2.2.2.1, ?_⟩
    intro S₀ Nd₀ hWT₀ hDisj₀
    obtain ⟨S', Nd', hsub, hWT', hOg', hFo', hQ'⟩ := hws.2.2.2.2 S₀ Nd₀ hWT₀ hDisj₀
    refine ⟨S', Nd', hsub, hWT', hOg', hFo', ?_⟩
    intro v hv
    obtain ⟨w', hw', hd'⟩ := hQ' v hv
    exact ⟨w', hw', by dsimp only at hd' ⊢; rwa [hn_loc] at hd'⟩
  obtain ⟨S', Nd', hc_post, htd_post, hreqs_nz, _, _⟩ :=
    trackedDisjIn_alloc_result hc_ce htd_ce hfb hws'
  have h128 : (128 + 7) / 8 * 8 = 128 := rfl
  rw [h128] at htd_post
  have htd_post' : TrackedDisjIn post S' Nd' w_si.toNat w_hdr.toNat
      [(memW post (globN post "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW post (globN post "bo" + 32) + 16, 16 * w_ntx.toNat),
       (w_reqs.toNat, 128)] := by
    rw [hbo_eq, hmemW_eq, hmemW_eq]; exact htd_post
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
  set resumed := setVarHOLFinite (ofString "reqs") (.val (.word w_reqs)) { post with locals := s.locals }
  refine ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_reqs, S', Nd',
    (blockContext_with_locals post _ post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    ⟨(trackedBlocks_with_locals post _ post.clock S' Nd' _).2 htd_post'.1,
      htd_post'.2.1, htd_post'.2.2.1, htd_post'.2.2.2⟩,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "reqs" ≠ ofString "si" from by decide, hsi],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "reqs" ≠ ofString "hdr" from by decide, hhdr],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "reqs" ≠ ofString "pl" from by decide, hpl],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "reqs" ≠ ofString "ntx" from by decide, hntx],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "reqs" ≠ ofString "txs" from by decide, htxs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "reqs" ≠ ofString "rcs" from by decide, hrcs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by change w_pl.toNat = memW post w_si.toNat; rw [hmemW_eq]; exact hpl_eq,
    by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hmemW_eq]; exact hntx_eq,
    hntx_le,
    by change globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
    htxs_nz, hrcs_nz,
    by change memW post (globN post "bo" + 24) = w_txs.toNat; rw [hbo_eq, hmemW_eq]; exact h24,
    by change memW post (globN post "bo" + 32) = w_rcs.toNat; rw [hbo_eq, hmemW_eq]; exact h32,
    by change memW post (globN post "bo" + 40) ≠ 0; rw [hbo_eq, hmemW_eq]; exact h40_nz,
    hreqs_nz,
    ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩, ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩,
    fun off hoff => by change memW post (globN post "bo" + off) = 0; rw [hbo_eq, hmemW_eq]; exact hz off hoff⟩

private def BoAfterStore56 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w_ntx.toNat)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧
    memW s (globN s "bo" + 56) ≠ 0 ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    (∀ off ∈ ([64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)

private theorem boAfterStore56_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : BoAfterStore56 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := h; exact hc.arena.1

private theorem hoare_store_bo_56 :
    Hoare BoAfterReqsAlloc
      (.store (.op .add [.var .global (ofString "bo"), .const 56#64]) (.var .local (ofString "reqs")))
      (fun r t => r = none → BoAfterStore56 t) := by
  apply Hoare.store_fall
  intro F s x v mem' hP hx hv hst
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_reqs, S, Nd, hc, htd,
    hsi, hhdr, hpl, hntx, htxs, hrcs, hreqs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40_nz,
    hreqs_nz, hin_txs, hin_rcs, hz⟩ := hP
  have hv_eq : v = .val (.word w_reqs) := by
    simpa [evalAt, evalHOLExact, hreqs] using hv.symm
  subst hv_eq
  obtain ⟨_, hsame, hframe⟩ := panMemStoresHOL_word_spec (s := s) (by simpa [flattenHOL] using hst)
  have hx_eq := evalAt_add_global_bo_const hc.arena.2 hc.world hbo_nz (off := 56) (by decide) hx
  obtain ⟨hc_p, htd_p, hbo_nz_p, _, _, h40_p, h56_p, hz_p⟩ :=
    bo_store_56 hc htd hbo_nz (by rw [h24]; exact htxs_nz) (by rw [h32]; exact hrcs_nz)
      h40_nz hreqs_nz hz hx_eq hsame hframe
  set post := { s with memory := mem' }
  have h24_p : memW post (globN post "bo" + 24) = w_txs.toNat := by
    rw [show globN post "bo" = globN s "bo" from rfl,
      memW_bo_store_ne hc.arena.2 hc.world hbo_nz (by decide) (by decide) hx_eq hframe, h24]
  have h32_p : memW post (globN post "bo" + 32) = w_rcs.toNat := by
    rw [show globN post "bo" = globN s "bo" from rfl,
      memW_bo_store_ne hc.arena.2 hc.world hbo_nz (by decide) (by decide) hx_eq hframe, h32]
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hbo_mem_ow := bo_in_worldOwned (S := S) (Nd := Nd) hbo_nz
  have hx_in_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hu_reg : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat, IvlUnhit s post c := by
    intro c hcm
    obtain ⟨hc8, _, _, _, hd_ow⟩ := hc.regions c hcm
    exact ivlUnhit_of_single_cell_disj (fun _ => hc8) hframe
      (disj_of_inside_left hx_in_bo (hd_ow _ hbo_mem_ow).flip).flip
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc_p, htd_p, hsi, hhdr, hpl, hntx, htxs, hrcs,
    by rw [hsi0_eq]; exact hpl_eq,
    by rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le, hbo_nz_p, htxs_nz, hrcs_nz, h24_p, h32_p, h40_p,
    by rw [h56_p]; exact hreqs_nz,
    hin_txs, hin_rcs, hz_p⟩

private def BoAfterRlsNew : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs w_rls : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w_ntx.toNat),
       (w_rls.toNat, 24), (memW s w_rls.toNat, 128)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    s.locals.lookup (ofString "rls") = some (.val (.word w_rls)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧
    memW s (globN s "bo" + 56) ≠ 0 ∧
    w_rls.toNat ≠ 0 ∧
    memW s w_rls.toNat ≠ 0 ∧
    memW s (w_rls.toNat + 8) = 0 ∧
    memW s (w_rls.toNat + 16) = 16 ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    (∀ off ∈ ([64, 72, 80] : List Nat), memW s (globN s "bo" + off) = 0)

private theorem resumeOn_lst_new_rls
    (wlst : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoidsIf (fun s => locN s "esz" * locN s "cap" < 2 ^ 64)
        (fun s post w => [(w, 24), (memW post w, locN s "esz" * locN s "cap")])) (ofString "lst_new"))
    (rtlst : Returns ArenaReady (fun s post l =>
        locN s "esz" * locN s "cap" < 2 ^ 64 → 1 ≤ locN s "cap" →
          FreshBlock s post l 24 ∧ FreshBlock s post (memW post l) (locN s "esz" * locN s "cap") ∧
          Disj (l, 24) (memW post l, locN s "esz" * locN s "cap") ∧
          memW post (l + 8) = 0 ∧ memW post (l + 16) = locN s "cap")
      (ofString "lst_new")) :
    DecCallResumeOn BoAfterStore56 BoAfterRlsNew (ofString "rls") (ofString "lst_new")
      [.const 8#64, .const 16#64] := by
  intro F s values body callee ret value post hcode hP hargs hl hrun
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, htd, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40_nz, h56_nz, hin_txs, hin_rcs, hz⟩ := hP
  have hpc := callee_param_two s (ofString "lst_new") (ofString "esz") (ofString "cap") .one .one _ _
    (by rw [hcode]; exact lookup_lst_new_fn) _ _ (.val (.word 8#64)) (.val (.word 16#64))
    values body callee ret rfl rfl hargs hl
  have hesz_loc : locN (callEntryStateHOLFinite s callee) "esz" = 8 := by
    simp [locN, callEntryStateHOLFinite, hpc.2.1]
  have hcap_loc : locN (callEntryStateHOLFinite s callee) "cap" = 16 := by
    simp [locN, callEntryStateHOLFinite, hpc.2.2]
  have hstep := FunSpec.at_lookup wlst s hcode values body callee ret hl
    (localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc)) (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  have hrt := FunSpec.at_lookup rtlst s hcode values body callee ret hl
    (localsFree_arenaReady s callee (s.clock - 1) hc.arena) (by rw [hrun]; simp)
  rw [hrun] at hrt; dsimp only at hrt
  obtain ⟨w_rls, rfl, _, _, hfb_imp⟩ := hrt value rfl
  have hfb_all := hfb_imp (by rw [hesz_loc, hcap_loc]; decide) (by rw [hcap_loc]; decide)
  rw [hesz_loc, hcap_loc] at hfb_all
  have hmul128 : 8 * 16 = 128 := rfl
  rw [hmul128] at hfb_all
  obtain ⟨hhead, hdata, hd_hd, hlen, hcap⟩ := hfb_all
  have hc_ce : BlockContext (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  have htd_ce : TrackedDisjIn (callEntryStateHOLFinite s callee) S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w_ntx.toNat)] :=
    ⟨(trackedBlocks_with_locals s callee (s.clock - 1) S Nd _).2 htd.1, htd.2.1, htd.2.2.1, htd.2.2.2⟩
  have hws' : WorldStep (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun _ post p => [(p, 24), (memW post p, 128)]))
      (callEntryStateHOLFinite s callee) (some (.returned (.val (.word w_rls)))) post := by
    refine ⟨hws.1, hws.2.1, hws.2.2.1, hws.2.2.2.1, ?_⟩
    intro S₀ Nd₀ hWT₀ hDisj₀
    obtain ⟨S', Nd', hsub, hWT', hOg', hFo', hQ'⟩ := hws.2.2.2.2 S₀ Nd₀ hWT₀ hDisj₀
    refine ⟨S', Nd', hsub, hWT', hOg', hFo', ?_⟩
    intro v hv
    have hQ'' := hQ' (by dsimp only; rw [hesz_loc, hcap_loc]; decide) v hv
    obtain ⟨w', hw', hd'⟩ := hQ''
    exact ⟨w', hw', by dsimp only at hd' ⊢; rwa [hesz_loc, hcap_loc] at hd'⟩
  obtain ⟨S', Nd', hc_post, htd_post, _, hrls_nz, hrls0_nz, hu_reg, _⟩ :=
    trackedDisjIn_lst_new_result hc_ce htd_ce hhead hdata hd_hd hlen hcap hws'
  have hbo_slot : ∀ off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat),
      globN post "bo" = globN s "bo" ∧ memW post (globN post "bo" + off) = memW s (globN s "bo" + off) := by
    intro off hoff
    have hoff_keep : off ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80] : List Nat) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    have hoff8 : off % 8 = 0 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hoff_lt : off + 8 ≤ 88 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
      rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact bo_slot_eq_of_worldStep (s := callEntryStateHOLFinite s callee)
      hc_ce.arena.2 hc_ce.world (by exact hbo_nz) hws'
      (by decide) (by simp) hoff_keep hoff8 hoff_lt (by intro _ hm; cases hm) (by intro _ hm; cases hm)
  have hbo_eq : globN post "bo" = globN s "bo" := (hbo_slot 24 (by simp)).1
  have h24_post : memW post (globN post "bo" + 24) = w_txs.toNat := by
    rw [(hbo_slot 24 (by simp)).2]; exact h24
  have h32_post : memW post (globN post "bo" + 32) = w_rcs.toNat := by
    rw [(hbo_slot 32 (by simp)).2]; exact h32
  have h40_post : memW post (globN post "bo" + 40) ≠ 0 := by
    rw [(hbo_slot 40 (by simp)).2]; exact h40_nz
  have h56_post : memW post (globN post "bo" + 56) ≠ 0 := by
    rw [(hbo_slot 56 (by simp)).2]; exact h56_nz
  have htd_post' : TrackedDisjIn post S' Nd' w_si.toNat w_hdr.toNat
      [(memW post (globN post "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW post (globN post "bo" + 32) + 16, 16 * w_ntx.toNat),
       (w_rls.toNat, 24), (memW post w_rls.toNat, 128)] := by
    rw [(hbo_slot 24 (by simp)).2, (hbo_slot 32 (by simp)).2]; exact htd_post
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
  set resumed := setVarHOLFinite (ofString "rls") (.val (.word w_rls)) { post with locals := s.locals }
  refine ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_rls, S', Nd',
    (blockContext_with_locals post _ post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    ⟨(trackedBlocks_with_locals post _ post.clock S' Nd' _).2 htd_post'.1,
      htd_post'.2.1, htd_post'.2.2.1, htd_post'.2.2.2⟩,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rls" ≠ ofString "si" from by decide, hsi],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rls" ≠ ofString "hdr" from by decide, hhdr],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rls" ≠ ofString "pl" from by decide, hpl],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rls" ≠ ofString "ntx" from by decide, hntx],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rls" ≠ ofString "txs" from by decide, htxs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "rls" ≠ ofString "rcs" from by decide, hrcs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by change w_pl.toNat = memW post w_si.toNat; rw [hsi0_eq]; exact hpl_eq,
    by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le,
    by change globN post "bo" ≠ 0; rw [hbo_eq]; exact hbo_nz,
    htxs_nz, hrcs_nz, h24_post, h32_post, h40_post, h56_post,
    hrls_nz, hrls0_nz, hlen, hcap,
    ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩, ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩,
    fun off hoff => by
      change memW post (globN post "bo" + off) = 0
      have hoff' : off ∈ ([24, 32, 40, 56, 64, 72, 80] : List Nat) := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff ⊢
        rcases hoff with rfl | rfl | rfl <;> simp
      rw [(hbo_slot off hoff').2]; exact hz off hoff⟩

private def BoAfterStore72 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TrackedDisjIn s S Nd w_si.toNat w_hdr.toNat
      [(memW s (globN s "bo" + 24) + 16, 16 * w_ntx.toNat),
       (memW s (globN s "bo" + 32) + 16, 16 * w_ntx.toNat)] ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧
    memW s (globN s "bo" + 56) ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    memW s (globN s "bo" + 72) ≠ 0 ∧
    memW s (globN s "bo" + 80) = 0 ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr")

private def BoInitialized : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧
    memW s (globN s "bo" + 56) ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    memW s (globN s "bo" + 72) ≠ 0 ∧
    memW s (globN s "bo" + 80) = w_ntx.toNat ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr")

private theorem boInitialized_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : BoInitialized s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := h; exact hc.arena.1

private theorem hoare_store_bo_72 :
    Hoare BoAfterRlsNew
      (.store (.op .add [.var .global (ofString "bo"), .const 72#64]) (.var .local (ofString "rls")))
      (fun r t => r = none → BoAfterStore72 t) := by
  apply Hoare.store_fall
  intro F s x v mem' hP hx hv hst
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_rls, S, Nd, hc, htd,
    hsi, hhdr, hpl, hntx, htxs, hrcs, hrls,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40_nz, h56_nz,
    hrls_nz, hrls0_nz, hlen, hcap, hin_txs, hin_rcs, hz⟩ := hP
  have hv_eq : v = .val (.word w_rls) := by
    simpa [evalAt, evalHOLExact, hrls] using hv.symm
  subst hv_eq
  obtain ⟨_, hsame, hframe⟩ := panMemStoresHOL_word_spec (s := s) (by simpa [flattenHOL] using hst)
  have hx_eq := evalAt_add_global_bo_const hc.arena.2 hc.world hbo_nz (off := 72) (by decide) hx
  obtain ⟨hc_p, htd_p, hbo_nz_p, _, _, h40_p, h56_p, h64_p, h72_p, h80_p⟩ :=
    bo_store_72 hc htd hbo_nz (by rw [h24]; exact htxs_nz) (by rw [h32]; exact hrcs_nz)
      h40_nz h56_nz hrls_nz hrls0_nz hlen hcap hz hx_eq hsame hframe
  set post := { s with memory := mem' }
  have h24_p : memW post (globN post "bo" + 24) = w_txs.toNat := by
    rw [show globN post "bo" = globN s "bo" from rfl,
      memW_bo_store_ne hc.arena.2 hc.world hbo_nz (by decide) (by decide) hx_eq hframe, h24]
  have h32_p : memW post (globN post "bo" + 32) = w_rcs.toNat := by
    rw [show globN post "bo" = globN s "bo" from rfl,
      memW_bo_store_ne hc.arena.2 hc.world hbo_nz (by decide) (by decide) hx_eq hframe, h32]
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hbo_mem_ow := bo_in_worldOwned (S := S) (Nd := Nd) hbo_nz
  have hx_in_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hu_reg : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat, IvlUnhit s post c := by
    intro c hcm
    obtain ⟨hc8, _, _, _, hd_ow⟩ := hc.regions c hcm
    exact ivlUnhit_of_single_cell_disj (fun _ => hc8) hframe
      (disj_of_inside_left hx_in_bo (hd_ow _ hbo_mem_ow).flip).flip
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc_p, htd_p, hsi, hhdr, hpl, hntx, htxs, hrcs,
    by rw [hsi0_eq]; exact hpl_eq,
    by rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le, hbo_nz_p, htxs_nz, hrcs_nz, h24_p, h32_p, h40_p, h56_p, h64_p,
    by rw [h72_p]; exact hrls_nz, h80_p,
    hin_txs, hin_rcs⟩

private theorem hoare_store_bo_80 :
    Hoare BoAfterStore72
      (.store (.op .add [.var .global (ofString "bo"), .const 80#64]) (.var .local (ofString "ntx")))
      (fun r t => r = none → BoInitialized t) := by
  apply Hoare.store_fall
  intro F s x v mem' hP hx hv hst
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, htd,
    hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40_nz, h56_nz, h64_z, h72_nz, h80_z,
    hin_txs, hin_rcs⟩ := hP
  have hv_eq : v = .val (.word w_ntx) := by
    simpa [evalAt, evalHOLExact, hntx] using hv.symm
  subst hv_eq
  obtain ⟨_, hsame, hframe⟩ := panMemStoresHOL_word_spec (s := s) (by simpa [flattenHOL] using hst)
  have hx_eq := evalAt_add_global_bo_const hc.arena.2 hc.world hbo_nz (off := 80) (by decide) hx
  obtain ⟨hc_p, hbo_nz_p, _, _, h40_p, h56_p, h64_p, h72_p, h80_p⟩ :=
    bo_store_80 hc htd hbo_nz (by rw [h24]; exact htxs_nz) (by rw [h32]; exact hrcs_nz)
      h40_nz h56_nz h64_z h72_nz h80_z hx_eq hsame hframe
  set post := { s with memory := mem' }
  have h24_p : memW post (globN post "bo" + 24) = w_txs.toNat := by
    rw [show globN post "bo" = globN s "bo" from rfl,
      memW_bo_store_ne hc.arena.2 hc.world hbo_nz (by decide) (by decide) hx_eq hframe, h24]
  have h32_p : memW post (globN post "bo" + 32) = w_rcs.toNat := by
    rw [show globN post "bo" = globN s "bo" from rfl,
      memW_bo_store_ne hc.arena.2 hc.world hbo_nz (by decide) (by decide) hx_eq hframe, h32]
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hbo_mem_ow := bo_in_worldOwned (S := S) (Nd := Nd) hbo_nz
  have hx_in_bo : Inside (x.toNat, 8) (globN s "bo") (globN s "bo" + 88) := by
    unfold Inside; dsimp; omega
  have hu_reg : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat, IvlUnhit s post c := by
    intro c hcm
    obtain ⟨hc8, _, _, _, hd_ow⟩ := hc.regions c hcm
    exact ivlUnhit_of_single_cell_disj (fun _ => hc8) hframe
      (disj_of_inside_left hx_in_bo (hd_ow _ hbo_mem_ow).flip).flip
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc_p, hsi, hhdr, hpl, hntx, htxs, hrcs,
    by rw [hsi0_eq]; exact hpl_eq,
    by rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le, hbo_nz_p, htxs_nz, hrcs_nz, h24_p, h32_p, h40_p, h56_p, h64_p, h72_p, h80_p,
    hin_txs, hin_rcs⟩

private theorem boInitialized_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : BoInitialized s) : WorldOK s := by
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := h; exact blockContext_worldOK hc

private theorem localsOnly_boInitialized :
    LocalsOnly ["si", "hdr", "pl", "ntx", "txs", "rcs"] BoInitialized := by
  intro F s locals k hl h
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs⟩ := h
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd,
    (blockContext_with_locals s locals k S Nd w_si.toNat w_hdr.toNat).2 hc,
    (hl "si" (by simp)).trans hsi,
    (hl "hdr" (by simp)).trans hhdr,
    (hl "pl" (by simp)).trans hpl,
    (hl "ntx" (by simp)).trans hntx,
    (hl "txs" (by simp)).trans htxs,
    (hl "rcs" (by simp)).trans hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs⟩

private theorem boInitialized_preserve_worldStep
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl}
    {gw : List String} {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {v : ValueHOL 64}
    {boKeep : List Nat}
    (hP : BoInitialized s)
    (hstep : WorldStep R gw keep Q (callEntryStateHOLFinite s callee) (some (.returned v)) post)
    (hjc : ofString "journal_cap" ∉ gw.map ofString)
    (hwd : ofString "wd_rlp_slices" ∉ gw.map ofString)
    (hbh : ofString "block_hashes" ∉ gw.map ofString)
    (hbhn : ofString "block_hashes_n" ∉ gw.map ofString)
    (hbo_gw : ofString "bo" ∉ gw.map ofString)
    (hkeep : ("bo", boKeep) ∈ keep)
    (hk24 : 24 ∈ boKeep) (hk32 : 32 ∈ boKeep) (hk40 : 40 ∈ boKeep)
    (hk56 : 56 ∈ boKeep) (hk64 : 64 ∈ boKeep) (hk72 : 72 ∈ boKeep) (hk80 : 80 ∈ boKeep)
    (hR0 : ∀ j ∈ R (callEntryStateHOLFinite s callee), j.2 = 0 → j.1 % 8 = 0)
    (hRtyped : ∀ S Nd, WorldTypedWith (callEntryStateHOLFinite s callee) S Nd →
      IvlsDisj (R (callEntryStateHOLFinite s callee)) (worldTypedIvls (callEntryStateHOLFinite s callee) S Nd))
    (hRtb : ∀ S Nd {bs : List Ivl}, WorldTypedWith (callEntryStateHOLFinite s callee) S Nd →
      TrackedBlocks (callEntryStateHOLFinite s callee) S Nd bs →
      IvlsDisj bs (R (callEntryStateHOLFinite s callee))) :
    BoInitialized { post with locals := s.locals } := by
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs⟩ := hP
  set ce := callEntryStateHOLFinite s callee
  have hc_ce : BlockContext ce S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  have hRt := hRtyped S Nd hc_ce.world
  obtain ⟨S', Nd', hc_post, _, hu_reg, _, _⟩ :=
    blockContext_worldStep hc_ce (by simp [TrackedBlocks] : TrackedBlocks ce S Nd []) hstep
      hjc hwd hbh hbhn hR0 hRt (hRtb S Nd hc_ce.world hc_ce.regions)
      (fun hnz => hRtb S Nd hc_ce.world (hc_ce.hashes hnz)) (by simp [IvlsDisj])
  have h24_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := boKeep) (off := 24)
    hc_ce.arena.2 hc_ce.world hbo_nz hstep hbo_gw hkeep hk24 (by decide) (by decide) hR0 hRt
  have h32_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := boKeep) (off := 32)
    hc_ce.arena.2 hc_ce.world hbo_nz hstep hbo_gw hkeep hk32 (by decide) (by decide) hR0 hRt
  have h40_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := boKeep) (off := 40)
    hc_ce.arena.2 hc_ce.world hbo_nz hstep hbo_gw hkeep hk40 (by decide) (by decide) hR0 hRt
  have h56_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := boKeep) (off := 56)
    hc_ce.arena.2 hc_ce.world hbo_nz hstep hbo_gw hkeep hk56 (by decide) (by decide) hR0 hRt
  have h64_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := boKeep) (off := 64)
    hc_ce.arena.2 hc_ce.world hbo_nz hstep hbo_gw hkeep hk64 (by decide) (by decide) hR0 hRt
  have h72_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := boKeep) (off := 72)
    hc_ce.arena.2 hc_ce.world hbo_nz hstep hbo_gw hkeep hk72 (by decide) (by decide) hR0 hRt
  have h80_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := boKeep) (off := 80)
    hc_ce.arena.2 hc_ce.world hbo_nz hstep hbo_gw hkeep hk80 (by decide) (by decide) hR0 hRt
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hstep.2.1
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S', Nd',
    (blockContext_with_locals post s.locals post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    hsi, hhdr, hpl, hntx, htxs, hrcs,
    by change w_pl.toNat = memW post w_si.toNat; rw [hsi0_eq]; exact hpl_eq,
    by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    hntx_le,
    by change globN post "bo" ≠ 0; rw [h24_eq.1]; exact hbo_nz,
    htxs_nz, hrcs_nz,
    by change memW post (globN post "bo" + 24) = w_txs.toNat; rw [h24_eq.2]; exact h24,
    by change memW post (globN post "bo" + 32) = w_rcs.toNat; rw [h32_eq.2]; exact h32,
    by change memW post (globN post "bo" + 40) ≠ 0; rw [h40_eq.2]; exact h40,
    by change memW post (globN post "bo" + 56) ≠ 0; rw [h56_eq.2]; exact h56,
    by change memW post (globN post "bo" + 64) = 0; rw [h64_eq.2]; exact h64,
    by change memW post (globN post "bo" + 72) ≠ 0; rw [h72_eq.2]; exact h72,
    by change memW post (globN post "bo" + 80) = w_ntx.toNat; rw [h80_eq.2]; exact h80,
    ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩,
    ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩⟩

private theorem hoare_bal_init_boInit
    (wbi : WorldKeeps WorldOK (fun _ => [])
      ["bal_accounts", "bal_idx_accts", "bal_idx_stor", "bal_index", "bal_key_buf", "heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "bal_init")) :
    Hoare BoInitialized
      (.call (some (none, none)) (ofString "bal_init") [])
      (fun r t => r = none → BoInitialized t) := by
  refine hoare_call_none_fall wbi
    (callEntryOn_of_imp localsFree_worldOK boInitialized_worldOK _ _) ?_
  intro F s callee post v _ hP hQc
  exact boInitialized_preserve_worldStep
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) hP (hQc (Or.inl ⟨v, rfl⟩))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp) (fun _ _ _ => by simp [IvlsDisj]) (fun _ _ _ _ => by simp [IvlsDisj])

private theorem hoare_systx_boInit (args : List (ExpHOL 64))
    (wsys : WorldKeeps WorldOK
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
      NoExtra (ofString "process_unchecked_system_transaction")) :
    Hoare BoInitialized
      (.call (some (none, none)) (ofString "process_unchecked_system_transaction") args)
      (fun r t => r = none → BoInitialized t) := by
  refine hoare_call_none_fall wsys
    (callEntryOn_of_imp localsFree_worldOK boInitialized_worldOK _ _) ?_
  intro F s callee post v _ hP hQc
  have ⟨_, _, _, _, _, _, S0, Nd0, hc0, _⟩ := hP
  have hc0_ce : BlockContext (callEntryStateHOLFinite s callee) S0 Nd0 _ _ :=
    (blockContext_with_locals s callee (s.clock - 1) S0 Nd0 _ _).2 hc0
  obtain ⟨hR0, _, _⟩ := bufferList16_disj_worldTypedIvls (callEntryStateHOLFinite s callee) hc0_ce.world
  exact boInitialized_preserve_worldStep
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) hP (hQc (Or.inl ⟨v, rfl⟩))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hR0
    (fun S Nd hWT => (bufferList16_disj_worldTypedIvls (callEntryStateHOLFinite s callee) hWT).2.1)
    (fun S Nd _ hWT hbs => (bufferList16_disj_worldTypedIvls (callEntryStateHOLFinite s callee) hWT).2.2 hbs)

private theorem hoare_state_fresh_tx_boInit
    (wsf : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "state_fresh_tx")) :
    Hoare BoInitialized
      (.call (some (none, none)) (ofString "state_fresh_tx") [])
      (fun r t => r = none → BoInitialized t) := by
  refine hoare_call_none_fall wsf
    (callEntryOn_of_imp localsFree_worldOK boInitialized_worldOK _ _) ?_
  intro F s callee post v _ hP hQc
  exact boInitialized_preserve_worldStep
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) hP (hQc (Or.inl ⟨v, rfl⟩))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp) (fun _ _ _ => by simp [IvlsDisj]) (fun _ _ _ _ => by simp [IvlsDisj])

private theorem hoare_track_ancestor_access_boInit
    (wtaa : WorldKeeps WorldOK (fun _ => [])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "track_ancestor_access")) :
    Hoare BoInitialized
      (.call (some (none, none)) (ofString "track_ancestor_access") [.const 1#64])
      (fun r t => r = none → BoInitialized t) := by
  refine hoare_call_none_fall wtaa
    (callEntryOn_of_imp localsFree_worldOK boInitialized_worldOK _ _) ?_
  intro F s callee post v _ hP hQc
  exact boInitialized_preserve_worldStep
    (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) hP (hQc (Or.inl ⟨v, rfl⟩))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp) (fun _ _ _ => by simp [IvlsDisj]) (fun _ _ _ _ => by simp [IvlsDisj])

private theorem hoare_ite_lasth_boInit :
    Hoare BoInitialized
      (.ite (.cmp .lower (.const 0#64) (.var .global (ofString "block_hashes_n")))
        (.assign .local (ofString "lasth")
          (.op .add [.var .global (ofString "block_hashes"),
            .panop .mul [.op .sub [.var .global (ofString "block_hashes_n"), .const 1#64], .const 32#64]]))
        .skip)
      (fun r t => r = none → BoInitialized t) := by
  apply Hoare.ite_fall
  · apply Hoare.assign_fall
    intro F s v ⟨hP, _⟩ _
    dsimp only [setKvarHOLFinite]
    exact localsOnly_boInitialized.setVar
      (fun n hn => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
        rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      v s hP
  · exact Hoare.skip fun _ ⟨hP, _⟩ _ => hP

private theorem evalAt_panOp_mul_const {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a : ExpHOL 64} {c : Nat} {v : ValueHOL 64}
    (hev : evalAt s (.panop .mul [a, .const (BitVec.ofNat 64 c)]) = some v) :
    ∃ wa : BitVec 64, evalAt s a = some (.val (.word wa)) ∧
      v = .val (.word (wa * BitVec.ofNat 64 c)) := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases ha : @evalHOLExact 64 F _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) a with _ | va
  · rw [ha] at hev; simp at hev
  · rw [ha] at hev; dsimp only at hev
    cases va with
    | val wl =>
      cases wl with
      | word wa =>
        simp only [List.all_cons, List.all_nil, Bool.and_true, List.map_cons, List.map_nil,
          valueIsWord, valueWord, panOpHOL, ↓reduceIte, Option.map_some, Option.some.injEq] at hev
        exact ⟨wa, ha, hev.symm⟩
    | rStruct _ => simp [valueIsWord] at hev
    | nStruct _ _ => simp [valueIsWord] at hev

private theorem evalAt_add3_words {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e1 e2 e3 : ExpHOL 64} {x : BitVec 64}
    (hev : evalAt s (.op .add [e1, e2, e3]) = some (.val (.word x))) :
    ∃ w1 w2 w3 : BitVec 64, evalAt s e1 = some (.val (.word w1)) ∧
      evalAt s e2 = some (.val (.word w2)) ∧
      evalAt s e3 = some (.val (.word w3)) ∧ x = w1 + (w2 + w3) := by
  simp only [evalAt, evalHOLExact, evalListHOLExact] at hev
  rcases h1 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e1 with _ | v1
  · rw [h1] at hev; simp at hev
  · rw [h1] at hev
    rcases h2 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e2 with _ | v2
    · rw [h2] at hev; simp at hev
    · rw [h2] at hev
      rcases h3 : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e3 with _ | v3
      · rw [h3] at hev; simp at hev
      · rw [h3] at hev; dsimp only at hev
        rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
        rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
        rcases v3 with ⟨⟨w3⟩⟩ | _ | _ <;> try simp [valueIsWord] at hev
        simp only [valueIsWord, Bool.and_self, ↓reduceIte, List.map, valueWord, wordOpHOL, wordOp,
          List.foldr, add_zero, Option.map, Option.some.injEq, ValueHOL.val.injEq,
          HolWordLab.word.injEq] at hev
        exact ⟨w1, w2, w3, h1, h2, h3, hev.symm⟩

private theorem while_signed_up_active_bounded_on
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (c b : MlS) (M : Nat) (hM : M < 2 ^ 63) {body : ProgHOL 64} {B : Nat}
    (hdec : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s → P (decClockHOLFinite s))
    (hsmall : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      ∀ wc wb : BitVec 64,
        s.locals.lookup c = some (.val (.word wc)) →
        s.locals.lookup b = some (.val (.word wb)) →
        wc.toNat < 2 ^ 63 ∧ wb.toNat ≤ M)
    (hbody : TerminatingProgBoundedOn
      (fun s => P s ∧ LoopActive (.cmp .less (.var .local c) (.var .local b)) s) body B)
    (hpres : Hoare (fun s => P s ∧ CondTrue (.cmp .less (.var .local c) (.var .local b)) s)
      body (fun r t => r = none → P t))
    (hncb : noContBreak body = true)
    (hstepC : StepsCounter c body) :
    TerminatingProgBoundedOn P (.while (.cmp .less (.var .local c) (.var .local b)) body)
      ((M + 1) * (B + 1)) := by
  refine TerminatingProgBoundedOn.while_rank_active (boundedCounterRank c M) hdec hbody ?_ ?_
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

private def PreLoopI : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs w_ptxs : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    s.locals.lookup (ofString "ptxs") = some (.val (.word w_ptxs)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ptxs.toNat = memW s (w_pl.toNat + 32) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧
    memW s (globN s "bo" + 56) ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    memW s (globN s "bo" + 72) ≠ 0 ∧
    memW s (globN s "bo" + 80) = w_ntx.toNat ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr")

private def TxLoopInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs w_ptxs w_i : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    s.locals.lookup (ofString "ptxs") = some (.val (.word w_ptxs)) ∧
    s.locals.lookup (ofString "i") = some (.val (.word w_i)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ptxs.toNat = memW s (w_pl.toNat + 32) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    w_i.toNat ≤ w_ntx.toNat ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧
    memW s (globN s "bo" + 56) ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    memW s (globN s "bo" + 72) ≠ 0 ∧
    memW s (globN s "bo" + 80) = w_ntx.toNat ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    BlockSliceLengths s w_i.toNat

private theorem localsOnly_txLoopInv :
    LocalsOnly ["si", "hdr", "pl", "ntx", "txs", "rcs", "ptxs", "i"] TxLoopInv := by
  intro F s locals k hl h
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, w_i, S, Nd,
    hc, hsi, hhdr, hpl, hntx, htxs, hrcs, hptxs, hi,
    hpl_eq, hntx_eq, hptxs_eq, hntx_le, hi_le,
    hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs, hsl⟩ := h
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, w_i, S, Nd,
    (blockContext_with_locals s locals k S Nd w_si.toNat w_hdr.toNat).2 hc,
    (hl "si" (by simp)).trans hsi,
    (hl "hdr" (by simp)).trans hhdr,
    (hl "pl" (by simp)).trans hpl,
    (hl "ntx" (by simp)).trans hntx,
    (hl "txs" (by simp)).trans htxs,
    (hl "rcs" (by simp)).trans hrcs,
    (hl "ptxs" (by simp)).trans hptxs,
    (hl "i" (by simp)).trans hi,
    hpl_eq, hntx_eq, hptxs_eq, hntx_le, hi_le,
    hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs,
    (blockSliceLengths_with_locals s locals k w_i.toNat).2 hsl⟩

private theorem txLoopInv_decClock {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : TxLoopInv s) : TxLoopInv (decClockHOLFinite s) :=
  localsOnly_txLoopInv s s.locals (s.clock - 1) (fun _ _ => rfl) h

private theorem txLoopInv_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : TxLoopInv s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hc, _⟩ := h; exact hc.arena.1

private theorem txLoopInv_worldOK {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : TxLoopInv s) : WorldOK s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hc, _⟩ := h; exact blockContext_worldOK hc

private theorem step_dec_ptxs {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hP : BoInitialized s)
    (hev : evalAt s (.load .one (.op .add [.var .local (ofString "pl"), .const 32#64])) = some v) :
    PreLoopI (setVarHOLFinite (ofString "ptxs") v s) := by
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd, hc, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le, hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs⟩ := hP
  obtain ⟨a, w_ptxs, ha, rfl, hptxs_mem, _, _, _⟩ := evalAt_load_one_word hc.arena.1 hev
  obtain ⟨w1, w2, hw1, hw2, rfl⟩ := evalAt_add2_words ha
  have hw1_eq : w1 = w_pl := by
    simp only [evalAt, evalHOLExact, hpl, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at hw1
    exact hw1.symm
  have hw2_eq : w2 = 32#64 := by
    simp only [evalAt, evalHOLExact, Option.some.injEq, ValueHOL.val.injEq,
      HolWordLab.word.injEq] at hw2
    exact hw2.symm
  subst w1; subst w2
  have hpl_in : (w_pl.toNat, 136) ∈ inputRegions s w_si.toNat w_hdr.toNat := by
    rw [hpl_eq]; simp [inputRegions]
  have hpl_hi : w_pl.toNat + 136 ≤ 2 ^ 64 :=
    (hc.regions _ hpl_in).2.2.1.2.trans (hc.arena.2.2.1.trans (by decide : heapLimit ≤ 2 ^ 64))
  have ha_nat : (w_pl + 32#64).toNat = w_pl.toNat + 32 := by
    rw [BitVec.toNat_add]; change (w_pl.toNat + 32) % 2 ^ 64 = w_pl.toNat + 32
    exact Nat.mod_eq_of_lt (by omega)
  rw [ha_nat] at hptxs_mem
  set t := setVarHOLFinite (ofString "ptxs") (.val (.word w_ptxs)) s
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, S, Nd,
    (blockContext_with_locals s _ s.clock S Nd w_si.toNat w_hdr.toNat).2 hc,
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "ptxs" ≠ ofString "si" from by decide, hsi],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "ptxs" ≠ ofString "hdr" from by decide, hhdr],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "ptxs" ≠ ofString "pl" from by decide, hpl],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "ptxs" ≠ ofString "ntx" from by decide, hntx],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "ptxs" ≠ ofString "txs" from by decide, htxs],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "ptxs" ≠ ofString "rcs" from by decide, hrcs],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    hpl_eq, hntx_eq, hptxs_mem, hntx_le, hbo_nz, htxs_nz, hrcs_nz,
    h24, h32, h40, h56, h64, h72, h80, hin_txs, hin_rcs⟩

private theorem step_dec_i_zero {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hP : PreLoopI s) :
    TxLoopInv (setVarHOLFinite (ofString "i") (.val (.word 0#64)) s) := by
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, S, Nd,
    hc, hsi, hhdr, hpl, hntx, htxs, hrcs, hptxs,
    hpl_eq, hntx_eq, hptxs_eq, hntx_le,
    hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs⟩ := hP
  set t := setVarHOLFinite (ofString "i") (.val (.word 0#64)) s
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, 0#64, S, Nd,
    (blockContext_with_locals s _ s.clock S Nd w_si.toNat w_hdr.toNat).2 hc,
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "si" from by decide, hsi],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "hdr" from by decide, hhdr],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "pl" from by decide, hpl],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "ntx" from by decide, hntx],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "txs" from by decide, htxs],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "rcs" from by decide, hrcs],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "ptxs" from by decide, hptxs],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    hpl_eq, hntx_eq, hptxs_eq, hntx_le, Nat.zero_le _,
    hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs, blockSliceLengths_zero _⟩

private theorem condTrue_i_lt_ntx {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w_i w_ntx : BitVec 64}
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w_i)))
    (hntx : s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)))
    (hi_le : w_i.toNat ≤ w_ntx.toNat)
    (hntx_le : w_ntx.toNat ≤ 1944059872)
    (hct : CondTrue (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s) :
    w_i.toNat < w_ntx.toNat := by
  obtain ⟨w, hw, hwnz⟩ := hct
  have hact : LoopActive (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s := by
    refine ⟨w, ?_, hwnz⟩
    rw [evalHOLFinite_eq_toExact]; exact hw
  obtain ⟨wc, wb, hlc, hlb, hslt⟩ := loopActive_cmp_less_locals hact
  have hwc : wc = w_i := by
    simpa [hi] using hlc.symm
  have hwb : wb = w_ntx := by
    simpa [hntx] using hlb.symm
  subst wc; subst wb
  simp only [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide] at hslt
  simp only [show ¬ w_i.toNat ≥ 2 ^ (64 - 1) by omega,
    show ¬ w_ntx.toNat ≥ 2 ^ (64 - 1) by omega, decide_false, Bool.false_eq_true,
    ↓reduceIte] at hslt
  omega

private theorem condFalse_i_eq_ntx {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w_i w_ntx : BitVec 64}
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w_i)))
    (hntx : s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)))
    (hi_le : w_i.toNat ≤ w_ntx.toNat)
    (hntx_le : w_ntx.toNat ≤ 1944059872)
    (hcf : CondFalse (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s) :
    w_i.toNat = w_ntx.toNat := by
  obtain ⟨wc, wb, hc, hb, hcmp⟩ :=
    evalAt_cmp s .less (.var .local (ofString "i")) (.var .local (ofString "ntx")) 0#64 hcf
  have hwc : wc = w_i := by
    simpa [evalAt, evalHOLExact, hi] using hc.symm
  have hwb : wb = w_ntx := by
    simpa [evalAt, evalHOLExact, hntx] using hb.symm
  subst wc; subst wb
  have hslt_eq : Compiler.Encoders.Asm.holAsmSignedLess w_i w_ntx = w_i.slt w_ntx := by
    simp only [Compiler.Encoders.Asm.holAsmSignedLess, BitVec.slt_eq_decide, BitVec.toInt_eq_msb_cond,
      BitVec.msb_eq_decide]
    repeat (any_goals first | split)
    all_goals simp_all only [decide_eq_true_eq]
    all_goals apply Bool.eq_iff_iff.mpr
    all_goals simp_all [decide_eq_true_eq]
    all_goals omega
  have hnot_lt : Compiler.Encoders.Asm.wordCmpHOL .less w_i w_ntx = false := by
    cases hc_b : Compiler.Encoders.Asm.wordCmpHOL .less w_i w_ntx
    · rfl
    · rw [hc_b] at hcmp; simp at hcmp
  have hge : ¬ w_i.toInt < w_ntx.toInt := by
    intro hlt_int
    have htrue : Compiler.Encoders.Asm.wordCmpHOL .less w_i w_ntx = true := by
      simpa only [Compiler.Encoders.Asm.wordCmpHOL, hslt_eq, BitVec.slt_iff_toInt_lt] using hlt_int
    rw [htrue] at hnot_lt; cases hnot_lt
  simp only [BitVec.toInt_eq_msb_cond, BitVec.msb_eq_decide] at hge
  simp only [show ¬ w_i.toNat ≥ 2 ^ (64 - 1) by omega,
    show ¬ w_ntx.toNat ≥ 2 ^ (64 - 1) by omega, decide_false, Bool.false_eq_true,
    ↓reduceIte] at hge
  omega

private def TxDecodedInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs w_ptxs w_i w_tx : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    TxAccessListAt s S Nd w_tx.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    s.locals.lookup (ofString "ptxs") = some (.val (.word w_ptxs)) ∧
    s.locals.lookup (ofString "i") = some (.val (.word w_i)) ∧
    s.locals.lookup (ofString "tx") = some (.val (.word w_tx)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ptxs.toNat = memW s (w_pl.toNat + 32) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    w_i.toNat < w_ntx.toNat ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧
    memW s (globN s "bo" + 56) ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    memW s (globN s "bo" + 72) ≠ 0 ∧
    memW s (globN s "bo" + 80) = w_ntx.toNat ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    BlockSliceLengths s w_i.toNat

private def TxProcessedInv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl w_ntx w_txs w_rcs w_ptxs w_i : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    s.locals.lookup (ofString "ntx") = some (.val (.word w_ntx)) ∧
    s.locals.lookup (ofString "txs") = some (.val (.word w_txs)) ∧
    s.locals.lookup (ofString "rcs") = some (.val (.word w_rcs)) ∧
    s.locals.lookup (ofString "ptxs") = some (.val (.word w_ptxs)) ∧
    s.locals.lookup (ofString "i") = some (.val (.word w_i)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    w_ntx.toNat = memW s (w_pl.toNat + 40) ∧
    w_ptxs.toNat = memW s (w_pl.toNat + 32) ∧
    w_ntx.toNat ≤ 1944059872 ∧
    w_i.toNat < w_ntx.toNat ∧
    globN s "bo" ≠ 0 ∧
    w_txs.toNat ≠ 0 ∧
    w_rcs.toNat ≠ 0 ∧
    memW s (globN s "bo" + 24) = w_txs.toNat ∧
    memW s (globN s "bo" + 32) = w_rcs.toNat ∧
    memW s (globN s "bo" + 40) ≠ 0 ∧
    memW s (globN s "bo" + 56) ≠ 0 ∧
    memW s (globN s "bo" + 64) = 0 ∧
    memW s (globN s "bo" + 72) ≠ 0 ∧
    memW s (globN s "bo" + 80) = w_ntx.toNat ∧
    Inside (w_txs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    Inside (w_rcs.toNat, 16 * w_ntx.toNat + 16) sourceBase (globN s "heap_ptr") ∧
    BlockSliceLengths s (w_i.toNat + 1)

private theorem txProcessedInv_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : TxProcessedInv s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hc, _⟩ := h; exact hc.arena.1

private theorem txValidAt_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k tx : Nat)
    (h : TxValidAt s tx) : TxValidAt { s with locals := locals, clock := k } tx := by
  obtain ⟨hw, hin, h0, h200, h216, hsl, h264, h280, hw208, hw272⟩ := h
  exact ⟨hw, hin, h0, h200, h216, hsl, h264, h280, hw208, hw272⟩

private theorem txAccessListAt_with_locals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (locals : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) {S Nd : List Nat} {tx : Nat}
    (h : TxAccessListAt s S Nd tx) :
    TxAccessListAt { s with locals := locals, clock := k } S Nd tx :=
  ⟨txValidAt_with_locals s locals k tx h.1, h.2.1, h.2.2⟩

private def decodeTxArgs : List (ExpHOL 64) :=
  [ .load .one (.op .add [.var .local (ofString "ptxs"),
      .panop .mul [.var .local (ofString "i"), .const 16#64]])
  , .load .one (.op .add [.var .local (ofString "ptxs"),
      .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64]) ]

private theorem eval_decodeTxArgs {F : Type} {s : PanSemStateFiniteExact 64 F}
    {w_si w_hdr w_pl w_ntx w_ptxs w_i : BitVec 64} {S Nd : List Nat}
    {values : List (ValueHOL 64)} {body : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret : ShapeHOL}
    (hcode : s.code = originalRuntimeCode)
    (hc : BlockContext s S Nd w_si.toNat w_hdr.toNat)
    (hptxs : s.locals.lookup (ofString "ptxs") = some (.val (.word w_ptxs)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word w_i)))
    (hpl_eq : w_pl.toNat = memW s w_si.toNat)
    (hntx_eq : w_ntx.toNat = memW s (w_pl.toNat + 40))
    (hptxs_eq : w_ptxs.toNat = memW s (w_pl.toNat + 32))
    (hntx_le : w_ntx.toNat ≤ 1944059872)
    (hi_lt : w_i.toNat < w_ntx.toNat)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      decodeTxArgs = some values)
    (hl : lookupCodeHOLFinite s.code.lookup (ofString "decode_transaction") values =
      some (body, callee, ret)) :
    locN (callEntryStateHOLFinite s callee) "p" =
      memW s (memW s (memW s w_si.toNat + 32) + 16 * w_i.toNat) ∧
    locN (callEntryStateHOLFinite s callee) "len" =
      memW s (memW s (memW s w_si.toNat + 32) + 16 * w_i.toNat + 8) ∧
    DecodeTxReady (callEntryStateHOLFinite s callee) := by
  have hargs_ex : @evalListHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) decodeTxArgs = some values := by
    rwa [← evalListHOLFinite_eq_toExact]
  rcases he1 : evalAt s (.load .one (.op .add [.var .local (ofString "ptxs"),
      .panop .mul [.var .local (ofString "i"), .const 16#64]])) with _ | v1
  · simp [decodeTxArgs, evalListHOLExact, evalAt, he1] at hargs_ex
  rcases he2 : evalAt s (.load .one (.op .add [.var .local (ofString "ptxs"),
      .panop .mul [.var .local (ofString "i"), .const 16#64], .const 8#64])) with _ | v2
  · simp [decodeTxArgs, evalListHOLExact, evalAt, he1, he2] at hargs_ex
  obtain ⟨a1, w_p, ha1, rfl, hp_mem, _, _, _⟩ := evalAt_load_one_word hc.arena.1 he1
  obtain ⟨a2, w_len, ha2, rfl, hlen_mem, _, _, _⟩ := evalAt_load_one_word hc.arena.1 he2
  obtain ⟨u1, u2, hu1, hu2, rfl⟩ := evalAt_add2_words ha1
  obtain ⟨wi1, hwi1, hu2_eq⟩ := evalAt_panOp_mul_const (c := 16) hu2
  have hu1_eq : u1 = w_ptxs := by simpa [evalAt, evalHOLExact, hptxs] using hu1.symm
  have hwi1_eq : wi1 = w_i := by simpa [evalAt, evalHOLExact, hi] using hwi1.symm
  have hu2_val : u2 = w_i * 16#64 := by
    have h := ValueHOL.val.inj hu2_eq; rw [← hwi1_eq]; exact HolWordLab.word.inj h
  subst u1; subst wi1; subst u2
  obtain ⟨q1, q2, q3, hq1, hq2, hq3, rfl⟩ := evalAt_add3_words ha2
  obtain ⟨wi2, hwi2, hq2_eq⟩ := evalAt_panOp_mul_const (c := 16) hq2
  have hq1_eq : q1 = w_ptxs := by simpa [evalAt, evalHOLExact, hptxs] using hq1.symm
  have hwi2_eq : wi2 = w_i := by simpa [evalAt, evalHOLExact, hi] using hwi2.symm
  have hq2_val : q2 = w_i * 16#64 := by
    have h := ValueHOL.val.inj hq2_eq; rw [← hwi2_eq]; exact HolWordLab.word.inj h
  have hq3_eq : q3 = 8#64 := by simpa [evalAt, evalHOLExact] using hq3.symm
  subst q1; subst wi2; subst q2; subst q3
  have hptxs_in : (w_ptxs.toNat, 16 * w_ntx.toNat) ∈ inputRegions s w_si.toNat w_hdr.toNat := by
    rw [hptxs_eq, hntx_eq, hpl_eq]; simp [inputRegions]
  have hptxs_hi : w_ptxs.toNat + 16 * w_ntx.toNat ≤ 2 ^ 64 :=
    (hc.regions _ hptxs_in).2.2.1.2.trans (hc.arena.2.2.1.trans (by decide : heapLimit ≤ 2 ^ 64))
  have hmul_nat : (w_i * 16#64).toNat = 16 * w_i.toNat := by
    rw [BitVec.toNat_mul]
    change (w_i.toNat * 16) % 2 ^ 64 = 16 * w_i.toNat
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have ha1_nat : (w_ptxs + w_i * 16#64).toNat = w_ptxs.toNat + 16 * w_i.toNat := by
    rw [BitVec.toNat_add, hmul_nat]
    exact Nat.mod_eq_of_lt (by change w_ptxs.toNat + 16 * w_i.toNat < 2 ^ 64; omega)
  have ha2_nat : (w_ptxs + (w_i * 16#64 + 8#64)).toNat = w_ptxs.toNat + 16 * w_i.toNat + 8 := by
    have hsub_add : (w_i * 16#64 + 8#64).toNat = 16 * w_i.toNat + 8 := by
      rw [BitVec.toNat_add, hmul_nat]
      exact Nat.mod_eq_of_lt (by change 16 * w_i.toNat + 8 < 2 ^ 64; omega)
    rw [BitVec.toNat_add, hsub_add]
    rw [Nat.mod_eq_of_lt (by change w_ptxs.toNat + (16 * w_i.toNat + 8) < 2 ^ 64; omega)]
    omega
  rw [ha1_nat, hptxs_eq, hpl_eq] at hp_mem
  rw [ha2_nat, hptxs_eq, hpl_eq] at hlen_mem
  have hpc := callee_param_two s (ofString "decode_transaction")
    (ofString "p") (ofString "len") .one .one _ _
    (by rw [hcode]; exact lookup_decode_transaction_fn)
    _ _ (.val (.word w_p)) (.val (.word w_len)) values body callee ret
    he1 he2 hargs hl
  have hp_ce : locN (callEntryStateHOLFinite s callee) "p" =
      memW s (memW s (memW s w_si.toNat + 32) + 16 * w_i.toNat) := by
    simp [locN, callEntryStateHOLFinite, hpc.2.1, hp_mem]
  have hlen_ce : locN (callEntryStateHOLFinite s callee) "len" =
      memW s (memW s (memW s w_si.toNat + 32) + 16 * w_i.toNat + 8) := by
    simp [locN, callEntryStateHOLFinite, hpc.2.2, hlen_mem]
  have hi_lt_mem : w_i.toNat < memW s (memW s w_si.toNat + 40) := by
    rwa [← hpl_eq, ← hntx_eq]
  have hlen32 : memW s (memW s (memW s w_si.toNat + 32) + 16 * w_i.toNat + 8) < 2 ^ 32 :=
    hc.payload.2.2.2 w_i.toNat hi_lt_mem
  have hph : memW s (memW s (memW s w_si.toNat + 32) + 16 * w_i.toNat) +
      memW s (memW s (memW s w_si.toNat + 32) + 16 * w_i.toNat + 8) ≤ globN s "heap_ptr" :=
    hc.tx_heap w_i.toNat hi_lt_mem
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hc.arena.2.2.1
  have hhl_64 : heapLimit ≤ 2 ^ 64 := by decide
  refine ⟨hp_ce, hlen_ce, ?_⟩
  unfold DecodeTxReady
  rw [hp_ce, hlen_ce]
  have hglob_hp : globN (callEntryStateHOLFinite s callee) "heap_ptr" = globN s "heap_ptr" := rfl
  rw [hglob_hp]
  refine ⟨hlen32, hph.trans (hhp_lim.trans hhl_64), ?_⟩
  intro x hx y hy
  simp only [List.mem_singleton] at hx hy
  subst hx; subst hy
  unfold Disj
  dsimp only
  omega

private theorem resumeOn_decode_transaction_txLoop
    (wdt : WorldKeeps (fun s => WorldOK s ∧ DecodeTxReady s) (fun _ => [])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (fun s r post S Nd => RetDecodedTx s r post S Nd ∧ RetBoSlicesKept s r post S Nd)
      (ofString "decode_transaction")) :
    DecCallResumeOn
      (fun s => TxLoopInv s ∧ CondTrue (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s)
      TxDecodedInv
      (ofString "tx") (ofString "decode_transaction") decodeTxArgs := by
  intro F s values body callee ret value post hcode ⟨hP, hct⟩ hargs hl hrun
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, w_i, S, Nd,
    hc, hsi, hhdr, hpl, hntx, htxs, hrcs, hptxs, hi,
    hpl_eq, hntx_eq, hptxs_eq, hntx_le, hi_le,
    hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs, hsl⟩ := hP
  have hi_lt : w_i.toNat < w_ntx.toNat := condTrue_i_lt_ntx hi hntx hi_le hntx_le hct
  obtain ⟨_, _, hdtr⟩ :=
    eval_decodeTxArgs hcode hc hptxs hi hpl_eq hntx_eq hptxs_eq hntx_le hi_lt hargs hl
  set ce := callEntryStateHOLFinite s callee
  have hc_ce : BlockContext ce S Nd w_si.toNat w_hdr.toNat :=
    (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
  have hstep := FunSpec.at_lookup wdt s hcode values body callee ret hl
    ⟨blockContext_worldOK hc_ce, hdtr⟩ (by rw [hrun]; simp)
  rw [hrun] at hstep; dsimp only at hstep
  have hws := hstep (Or.inl ⟨value, rfl⟩)
  obtain ⟨S', Nd', hc_post, _, hu_reg, _, hq⟩ :=
    blockContext_worldStep hc_ce (by simp [TrackedBlocks] : TrackedBlocks ce S Nd []) hws
      (by decide) (by decide) (by decide) (by decide)
      (by simp) (by simp [IvlsDisj]) (by simp [IvlsDisj])
      (fun _ => by simp [IvlsDisj]) (by simp [IvlsDisj])
  obtain ⟨w_tx, rfl, htx_al⟩ := hq.1 value rfl
  have hsl_post : BlockSliceLengths post w_i.toNat :=
    blockSliceLengths_of_retBoSlicesKept (S := S') (Nd := Nd') hsl
      (by change w_i.toNat ≤ memW s (globN s "bo" + 80); omega) hq.2 rfl
  have h24_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 24)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp [IvlsDisj])
  have h32_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 32)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp [IvlsDisj])
  have h40_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 40)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp [IvlsDisj])
  have h56_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 56)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp [IvlsDisj])
  have h64_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 64)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp [IvlsDisj])
  have h72_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 72)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp [IvlsDisj])
  have h80_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80]) (off := 80)
    hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) (by simp) (by simp [IvlsDisj])
  have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
      c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
    fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
  have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
    simpa only [Nat.add_zero] using
      inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
        (off := 0) (by omega) (by omega)
  have hpl32_eq : memW post (memW s w_si.toNat + 32) = memW s (memW s w_si.toNat + 32) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 32) (by omega) (by omega)
  have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
    inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
      (off := 40) (by omega) (by omega)
  have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
  set resumed := setVarHOLFinite (ofString "tx") (.val (.word w_tx)) { post with locals := s.locals }
  have htx_al_res : TxAccessListAt resumed S' Nd' w_tx.toNat :=
    txAccessListAt_with_locals post resumed.locals post.clock htx_al
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, w_i, w_tx, S', Nd',
    (blockContext_with_locals post _ post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
    htx_al_res,
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tx" ≠ ofString "si" from by decide, hsi],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tx" ≠ ofString "hdr" from by decide, hhdr],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tx" ≠ ofString "pl" from by decide, hpl],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tx" ≠ ofString "ntx" from by decide, hntx],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tx" ≠ ofString "txs" from by decide, htxs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tx" ≠ ofString "rcs" from by decide, hrcs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tx" ≠ ofString "ptxs" from by decide, hptxs],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "tx" ≠ ofString "i" from by decide, hi],
    by simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    by change w_pl.toNat = memW post w_si.toNat; rw [hsi0_eq]; exact hpl_eq,
    by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
    by change w_ptxs.toNat = memW post (w_pl.toNat + 32); rw [hpl_eq, hpl32_eq, ← hpl_eq]; exact hptxs_eq,
    hntx_le, hi_lt,
    by change globN post "bo" ≠ 0; rw [h24_eq.1]; exact hbo_nz,
    htxs_nz, hrcs_nz,
    by change memW post (globN post "bo" + 24) = w_txs.toNat; rw [h24_eq.2]; exact h24,
    by change memW post (globN post "bo" + 32) = w_rcs.toNat; rw [h32_eq.2]; exact h32,
    by change memW post (globN post "bo" + 40) ≠ 0; rw [h40_eq.2]; exact h40,
    by change memW post (globN post "bo" + 56) ≠ 0; rw [h56_eq.2]; exact h56,
    by change memW post (globN post "bo" + 64) = 0; rw [h64_eq.2]; exact h64,
    by change memW post (globN post "bo" + 72) ≠ 0; rw [h72_eq.2]; exact h72,
    by change memW post (globN post "bo" + 80) = w_ntx.toNat; rw [h80_eq.2]; exact h80,
    ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩,
    ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩,
    (blockSliceLengths_with_locals post _ post.clock w_i.toNat).2 hsl_post⟩

private theorem resumeOn_decode_transaction_txLoop_active
    (wdt : WorldKeeps (fun s => WorldOK s ∧ DecodeTxReady s) (fun _ => [])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (fun s r post S Nd => RetDecodedTx s r post S Nd ∧ RetBoSlicesKept s r post S Nd)
      (ofString "decode_transaction")) :
    DecCallResumeOn
      (fun s => TxLoopInv s ∧ LoopActive (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s)
      TxDecodedInv
      (ofString "tx") (ofString "decode_transaction") decodeTxArgs := by
  intro F s values body callee ret value post hcode ⟨hP, hact⟩ hargs hl hrun
  have hct : CondTrue (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s := by
    obtain ⟨w, hw, hwnz⟩ := hact
    refine ⟨w, ?_, hwnz⟩
    rw [← evalHOLFinite_eq_toExact]; exact hw
  exact resumeOn_decode_transaction_txLoop wdt s values body callee ret value post
    hcode ⟨hP, hct⟩ hargs hl hrun

private theorem callEntryOn_process_transaction_txDecoded :
    CallEntryOn TxDecodedInv TxReadyStrong (ofString "process_transaction")
      [.var .local (ofString "tx"), .var .local (ofString "i")] := by
  intro F s values body callee ret hcode hP hargs hl
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, w_i, w_tx, S, Nd,
    hc, htx_al, hsi, hhdr, hpl, hntx, htxs, hrcs, hptxs, hi, htx,
    hpl_eq, hntx_eq, hptxs_eq, hntx_le, hi_lt,
    hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs, hsl⟩ := hP
  have hpc := callee_param_two s (ofString "process_transaction")
    (ofString "tx") (ofString "index") .one .one _ _
    (by rw [hcode]; exact lookup_process_transaction_fn)
    (.var .local (ofString "tx")) (.var .local (ofString "i"))
    (.val (.word w_tx)) (.val (.word w_i)) values body callee ret
    (by simp [evalAt, evalHOLExact, htx]) (by simp [evalAt, evalHOLExact, hi]) hargs hl
  set ce := callEntryStateHOLFinite s callee
  have htx_ce : locN ce "tx" = w_tx.toNat := by
    simp [ce, locN, callEntryStateHOLFinite, hpc.2.1]
  have hidx_ce : locN ce "index" = w_i.toNat := by
    simp [ce, locN, callEntryStateHOLFinite, hpc.2.2]
  have hW_ce : WorldOK ce :=
    localsFree_worldOK s callee (s.clock - 1) (blockContext_worldOK hc)
  have hWT_ce : WorldTypedWith ce S Nd :=
    (worldTypedWith_with_locals s callee (s.clock - 1) S Nd).2 hc.world
  have htx_al_ce : TxAccessListOK ce S Nd := by
    unfold TxAccessListOK
    rw [htx_ce]
    exact txAccessListAt_with_locals s callee (s.clock - 1) htx_al
  exact ⟨⟨hW_ce, hbo_nz,
    by change memW s (globN s "bo" + 24) ≠ 0; rw [h24]; exact htxs_nz,
    by change memW s (globN s "bo" + 32) ≠ 0; rw [h32]; exact hrcs_nz,
    by rw [hidx_ce]; change w_i.toNat < memW s (globN s "bo" + 80); rw [h80]; exact hi_lt⟩,
    hc.jcap_nz, h40, h72, S, Nd, hWT_ce, htx_al_ce⟩

private theorem hoare_process_transaction_txDecoded
    (wpt : WorldKeeps TxReadyStrong
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
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ RetTransactionSlices s r post S Nd)
      (ofString "process_transaction")) :
    Hoare TxDecodedInv
      (.call (some (none, none)) (ofString "process_transaction")
        [.var .local (ofString "tx"), .var .local (ofString "i")])
      (fun r t => r = none → TxProcessedInv t) := by
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  rcases hrun : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "process_transaction")
        [.var .local (ofString "tx"), .var .local (ofString "i")]) with ⟨r, t⟩
  rw [hrun] at hr; dsimp only at hr; subst hr
  rw [evaluateHOLFiniteState_call] at hrun
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "tx"), .var .local (ofString "i")] with _ | values
  · rw [hargs] at hrun; simp at hrun
  rw [hargs] at hrun; dsimp only at hrun
  rcases hl : lookupCodeHOLFinite s.code.lookup (ofString "process_transaction") values with
    _ | ⟨body, callee, ret⟩
  · rw [hl] at hrun; simp at hrun
  rw [hl] at hrun; dsimp only at hrun
  split_ifs at hrun with hz
  · simp at hrun
  rcases hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with ⟨bres, post⟩
  rw [hb] at hrun
  cases bres with
  | none => simp at hrun
  | some br =>
    cases br with
    | returned v =>
      dsimp only at hrun
      split_ifs at hrun with hsh
      · obtain ⟨_, ht_eq⟩ := Prod.mk.inj hrun
        subst ht_eq
        have hce_ready := callEntryOn_process_transaction_txDecoded s values body callee ret hcode hP hargs hl
        obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, w_i, w_tx, S, Nd,
          hc, _, hsi, hhdr, hpl, hntx, htxs, hrcs, hptxs, hi, htx,
          hpl_eq, hntx_eq, hptxs_eq, hntx_le, hi_lt,
          hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
          hin_txs, hin_rcs, hsl⟩ := hP
        have hpc := callee_param_two s (ofString "process_transaction")
          (ofString "tx") (ofString "index") .one .one _ _
          (by rw [hcode]; exact lookup_process_transaction_fn)
          (.var .local (ofString "tx")) (.var .local (ofString "i"))
          (.val (.word w_tx)) (.val (.word w_i)) values body callee ret
          (by simp [evalAt, evalHOLExact, htx]) (by simp [evalAt, evalHOLExact, hi]) hargs hl
        set ce := callEntryStateHOLFinite s callee
        have hidx_ce : locN ce "index" = w_i.toNat := by
          simp [ce, locN, callEntryStateHOLFinite, hpc.2.2]
        have hstep := FunSpec.at_lookup wpt s hcode values body callee ret hl hce_ready (by rw [hb]; simp)
        rw [hb] at hstep; dsimp only at hstep
        have hws := hstep (Or.inl ⟨v, rfl⟩)
        have hc_ce : BlockContext ce S Nd w_si.toNat w_hdr.toNat :=
          (blockContext_with_locals s callee (s.clock - 1) S Nd w_si.toNat w_hdr.toNat).2 hc
        obtain ⟨hR0, hRtyped, hRtb⟩ := bufferList16_disj_worldTypedIvls ce hc_ce.world
        obtain ⟨S', Nd', hc_post, _, hu_reg, _, hq⟩ :=
          blockContext_worldStep hc_ce (by simp [TrackedBlocks] : TrackedBlocks ce S Nd []) hws
            (by decide) (by decide) (by decide) (by decide)
            hR0 hRtyped (hRtb hc_ce.regions) (fun hnz => hRtb (hc_ce.hashes hnz)) (by simp [IvlsDisj])
        have hsl_ce : BlockSliceLengths ce (locN ce "index") := by
          rw [hidx_ce]; exact (blockSliceLengths_with_locals s callee (s.clock - 1) w_i.toNat).2 hsl
        have hsl_post : BlockSliceLengths post (w_i.toNat + 1) := by
          have h := blockSliceLengths_transaction hsl_ce hq.2 rfl
          rwa [hidx_ce] at h
        have h24_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [24, 32, 40, 56, 64, 72, 80]) (off := 24)
          hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
        have h32_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [24, 32, 40, 56, 64, 72, 80]) (off := 32)
          hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
        have h40_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [24, 32, 40, 56, 64, 72, 80]) (off := 40)
          hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
        have h56_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [24, 32, 40, 56, 64, 72, 80]) (off := 56)
          hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
        have h64_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [24, 32, 40, 56, 64, 72, 80]) (off := 64)
          hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
        have h72_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [24, 32, 40, 56, 64, 72, 80]) (off := 72)
          hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
        have h80_eq := bo_slot_eq_of_worldStep (s := ce) (boKeep := [24, 32, 40, 56, 64, 72, 80]) (off := 80)
          hc_ce.arena.2 hc_ce.world hbo_nz hws (by decide) (by decide) (by decide) (by decide) (by decide) hR0 hRtyped
        have hcin : ∀ c ∈ inputRegions s w_si.toNat w_hdr.toNat,
            c.1 % 8 = 0 ∧ Inside c sourceBase (globN s "heap_ptr") ∧ WordsOK s c :=
          fun c hm => ⟨(hc.regions c hm).1, (hc.regions c hm).2.2.1, (hc.regions c hm).2.2.2.1⟩
        have hsi0_eq : memW post w_si.toNat = memW s w_si.toNat := by
          simpa only [Nat.add_zero] using
            inputRegions_word_eq hc.arena hcin hu_reg (c := (w_si.toNat, 96)) (by simp [inputRegions])
              (off := 0) (by omega) (by omega)
        have hpl32_eq : memW post (memW s w_si.toNat + 32) = memW s (memW s w_si.toNat + 32) :=
          inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
            (off := 32) (by omega) (by omega)
        have hpl40_eq : memW post (memW s w_si.toNat + 40) = memW s (memW s w_si.toNat + 40) :=
          inputRegions_word_eq hc.arena hcin hu_reg (c := (memW s w_si.toNat, 136)) (by simp [inputRegions])
            (off := 40) (by omega) (by omega)
        have hhp_grow : globN s "heap_ptr" ≤ globN post "heap_ptr" := hws.2.1
        exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, w_i, S', Nd',
          (blockContext_with_locals post s.locals post.clock S' Nd' w_si.toNat w_hdr.toNat).2 hc_post,
          hsi, hhdr, hpl, hntx, htxs, hrcs, hptxs, hi,
          by change w_pl.toNat = memW post w_si.toNat; rw [hsi0_eq]; exact hpl_eq,
          by change w_ntx.toNat = memW post (w_pl.toNat + 40); rw [hpl_eq, hpl40_eq, ← hpl_eq]; exact hntx_eq,
          by change w_ptxs.toNat = memW post (w_pl.toNat + 32); rw [hpl_eq, hpl32_eq, ← hpl_eq]; exact hptxs_eq,
          hntx_le, hi_lt,
          by change globN post "bo" ≠ 0; rw [h24_eq.1]; exact hbo_nz,
          htxs_nz, hrcs_nz,
          by change memW post (globN post "bo" + 24) = w_txs.toNat; rw [h24_eq.2]; exact h24,
          by change memW post (globN post "bo" + 32) = w_rcs.toNat; rw [h32_eq.2]; exact h32,
          by change memW post (globN post "bo" + 40) ≠ 0; rw [h40_eq.2]; exact h40,
          by change memW post (globN post "bo" + 56) ≠ 0; rw [h56_eq.2]; exact h56,
          by change memW post (globN post "bo" + 64) = 0; rw [h64_eq.2]; exact h64,
          by change memW post (globN post "bo" + 72) ≠ 0; rw [h72_eq.2]; exact h72,
          by change memW post (globN post "bo" + 80) = w_ntx.toNat; rw [h80_eq.2]; exact h80,
          ⟨hin_txs.1, hin_txs.2.trans hhp_grow⟩,
          ⟨hin_rcs.1, hin_rcs.2.trans hhp_grow⟩,
          (blockSliceLengths_with_locals post s.locals post.clock (w_i.toNat + 1)).2 hsl_post⟩
      · simp at hrun
    | _ => simp at hrun

private theorem hoare_assign_inc_i_txLoop :
    Hoare TxProcessedInv
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64]))
      (fun r t => r = none → TxLoopInv t) := by
  apply Hoare.assign_fall
  intro F s v hP hev
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, w_i, S, Nd,
    hc, hsi, hhdr, hpl, hntx, htxs, hrcs, hptxs, hi,
    hpl_eq, hntx_eq, hptxs_eq, hntx_le, hi_lt,
    hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs, hsl⟩ := hP
  obtain ⟨w_new, rfl⟩ := evalAt_op_word hev
  obtain ⟨w1, w2, hw1, hw2, rfl⟩ := evalAt_add2_words hev
  have hw1_eq : w1 = w_i := by simpa [evalAt, evalHOLExact, hi] using hw1.symm
  have hw2_eq : w2 = 1#64 := by simpa [evalAt, evalHOLExact] using hw2.symm
  subst w1; subst w2
  have hnext_nat : (w_i + 1#64).toNat = w_i.toNat + 1 := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by change w_i.toNat + 1 < 2 ^ 64; omega)
  dsimp only [setKvarHOLFinite]
  set t := setVarHOLFinite (ofString "i") (.val (.word (w_i + 1#64))) s
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, w_i + 1#64, S, Nd,
    (blockContext_with_locals s _ s.clock S Nd w_si.toNat w_hdr.toNat).2 hc,
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "si" from by decide, hsi],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "hdr" from by decide, hhdr],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "pl" from by decide, hpl],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "ntx" from by decide, hntx],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "txs" from by decide, htxs],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "rcs" from by decide, hrcs],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "i" ≠ ofString "ptxs" from by decide, hptxs],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    hpl_eq, hntx_eq, hptxs_eq, hntx_le,
    by rw [hnext_nat]; omega,
    hbo_nz, htxs_nz, hrcs_nz, h24, h32, h40, h56, h64, h72, h80,
    hin_txs, hin_rcs,
    by rw [hnext_nat]; exact (blockSliceLengths_with_locals s _ s.clock (w_i.toNat + 1)).2 hsl⟩

private def progTxLoopBody : ProgHOL 64 :=
  .decCall (ofString "tx") .one (ofString "decode_transaction") decodeTxArgs
    (.seq .skip
      (.seq (.call (some (none, none)) (ofString "process_transaction")
              [.var .local (ofString "tx"), .var .local (ofString "i")])
        (.seq .skip
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])))))

private theorem hoare_txLoop_body
    (wdt : WorldKeeps (fun s => WorldOK s ∧ DecodeTxReady s) (fun _ => [])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (fun s r post S Nd => RetDecodedTx s r post S Nd ∧ RetBoSlicesKept s r post S Nd)
      (ofString "decode_transaction"))
    (wpt : WorldKeeps TxReadyStrong
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
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ RetTransactionSlices s r post S Nd)
      (ofString "process_transaction")) :
    Hoare
      (fun s => TxLoopInv s ∧ CondTrue (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s)
      progTxLoopBody
      (fun r t => r = none → TxLoopInv t) := by
  refine Hoare.decCall_fall
    (fun n hn => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    localsOnly_txLoopInv
    (resumeOn_decode_transaction_txLoop wdt) ?_
  exact hoare_seq_skip
    (Hoare.seq_fall (hoare_process_transaction_txDecoded wpt)
      (hoare_seq_skip hoare_assign_inc_i_txLoop))

private theorem terminating_txLoop
    (hdt : TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.«decode_transaction»)
    (hpt : TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction") K.«process_transaction»)
    (wdt : WorldKeeps (fun s => WorldOK s ∧ DecodeTxReady s) (fun _ => [])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (fun s r post S Nd => RetDecodedTx s r post S Nd ∧ RetBoSlicesKept s r post S Nd)
      (ofString "decode_transaction"))
    (wpt : WorldKeeps TxReadyStrong
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
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ RetTransactionSlices s r post S Nd)
      (ofString "process_transaction")) :
    TerminatingProgBoundedOn TxLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) progTxLoopBody)
      ((1944059872 + 1) * ((K.«decode_transaction» + 1) + (K.«process_transaction» + 1) + 1)) := by
  have hbody : TerminatingProgBoundedOn
      (fun {F} s => TxLoopInv s ∧ LoopActive (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s)
      progTxLoopBody ((K.«decode_transaction» + 1) + (K.«process_transaction» + 1)) := by
    intro F s hc hP
    exact
      (TerminatingProgBoundedOn.decCall_on
        (P := fun {F} s => TxLoopInv s ∧ LoopActive (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s)
        (Pc := GuestInv)
        (Q := TxDecodedInv)
        hdt (ofString "tx") .one decodeTxArgs
        (callEntryOn_of_imp localsFree_guestInv
          (P := fun {F} s => TxLoopInv s ∧ LoopActive (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) s)
          (fun s h => txLoopInv_guestInv s h.1) _ _)
        (resumeOn_decode_transaction_txLoop_active wdt)
        (seq_skip_on
          (TerminatingProgBoundedOn.seq_hoare_trans
            (TerminatingProgBoundedOn.call_on hpt none
              [.var .local (ofString "tx"), .var .local (ofString "i")]
              callEntryOn_process_transaction_txDecoded)
            (hoare_process_transaction_txDecoded wpt)
            (seq_skip_on
              (straight_on (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1#64])) rfl))))
        s hc hP).weaken (by omega)
  intro F s hc hP
  exact while_signed_up_active_bounded_on (ofString "i") (ofString "ntx") 1944059872 (by decide)
    txLoopInv_decClock
    (fun s' hP' wc wb hlc hlb => by
      obtain ⟨_, _, _, w_ntx, _, _, _, w_i, _, _, _, _, _, _, hntx, _, _, _, hi,
        _, _, _, hntx_le, hi_le, _⟩ := hP'
      have hwc : wc = w_i := by simpa [hi] using hlc.symm
      have hwb : wb = w_ntx := by simpa [hntx] using hlb.symm
      subst wc; subst wb
      exact ⟨by omega, hntx_le⟩)
    hbody
    (hoare_txLoop_body wdt wpt)
    (by rfl)
    (StepsCounter.decCall_ne (by decide) .one decodeTxArgs
      (StepsCounter.seq_keep (PreservesCounter.skip _)
        (StepsCounter.seq_keep (PreservesCounter.call_none _ _ _)
          (StepsCounter.seq_keep (PreservesCounter.skip _)
            (StepsCounter.assign_inc _)))))
    s hc hP

private theorem hoare_txLoop_exit
    (wdt : WorldKeeps (fun s => WorldOK s ∧ DecodeTxReady s) (fun _ => [])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (fun s r post S Nd => RetDecodedTx s r post S Nd ∧ RetBoSlicesKept s r post S Nd)
      (ofString "decode_transaction"))
    (wpt : WorldKeeps TxReadyStrong
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
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ RetTransactionSlices s r post S Nd)
      (ofString "process_transaction")) :
    Hoare TxLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) progTxLoopBody)
      (fun r t => r = none → PostLoopBase true t) := by
  have hw := hoare_while_ncb_condFalse txLoopInv_decClock (by rfl) (hoare_txLoop_body wdt wpt)
  refine ⟨fun {F} s hcode hP _ hr => ?_⟩
  obtain ⟨hInv, hcf⟩ := hw.run s hcode hP (by rw [hr]; simp) hr
  obtain ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, w_ptxs, w_i, S, Nd,
    hc, hsi, hhdr, hpl, hntx, htxs, hrcs, _, hi,
    hpl_eq, hntx_eq, _, hntx_le, hi_le,
    hbo_nz, htxs_nz, hrcs_nz, h24, h32, _, _, h64, _, h80,
    hin_txs, hin_rcs, hsl⟩ := hInv
  have hi_eq : w_i.toNat = w_ntx.toNat := condFalse_i_eq_ntx hi hntx hi_le hntx_le hcf
  rw [hi_eq] at hsl
  exact ⟨w_si, w_hdr, w_pl, w_ntx, w_txs, w_rcs, S, Nd,
    hc, hsi, hhdr, hpl, hntx, htxs, hrcs,
    hpl_eq, hntx_eq, hntx_le,
    hbo_nz, htxs_nz, hrcs_nz, h24, h32, h80,
    hin_txs, hin_rcs, hsl, fun _ => h64⟩

private def PreNtx : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
  ∃ w_si w_hdr w_pl : BitVec 64, ∃ S Nd : List Nat,
    BlockContext s S Nd w_si.toNat w_hdr.toNat ∧
    s.locals.lookup (ofString "si") = some (.val (.word w_si)) ∧
    s.locals.lookup (ofString "hdr") = some (.val (.word w_hdr)) ∧
    s.locals.lookup (ofString "pl") = some (.val (.word w_pl)) ∧
    w_pl.toNat = memW s w_si.toNat ∧
    memW s (w_pl.toNat + 40) ≤ 1944059872

private theorem step_dec_pl {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (h : BlockReadyExecStrong s)
    (hev : evalAt s (.load .one (.op .add [.var .local (ofString "si"), .const 0#64])) = some v) :
    PreNtx (setVarHOLFinite (ofString "pl") v s) := by
  obtain ⟨w_si, hsi⟩ := h.2.1 "si" (by simp)
  obtain ⟨w_hdr, hhdr⟩ := h.2.1 "hdr" (by simp)
  have hsi_loc : locN s "si" = w_si.toNat := by simp [locN, hsi]
  have hhdr_loc : locN s "hdr" = w_hdr.toNat := by simp [locN, hhdr]
  have hntx_le := blockReadyExecStrong_tx_count h
  obtain ⟨S, Nd, hc⟩ := blockContext_of_entry h.1 h.2.2
  rw [hsi_loc] at hntx_le
  rw [hsi_loc, hhdr_loc] at hc
  obtain ⟨a, w_pl, ha, rfl, hpl_eq, _, _, _⟩ := evalAt_load_one_word hc.arena.1 hev
  obtain ⟨w1, w2, hw1, hw2, rfl⟩ := evalAt_add2_words ha
  have hw1_eq : w1 = w_si := by simpa [evalAt, evalHOLExact, hsi] using hw1.symm
  have hw2_eq : w2 = 0#64 := by simpa [evalAt, evalHOLExact] using hw2.symm
  subst w1; subst w2
  have ha_eq : (w_si + 0#64).toNat = w_si.toNat := by simp
  rw [ha_eq] at hpl_eq
  set t := setVarHOLFinite (ofString "pl") (.val (.word w_pl)) s
  exact ⟨w_si, w_hdr, w_pl, S, Nd,
    (blockContext_with_locals s _ s.clock S Nd w_si.toNat w_hdr.toNat).2 hc,
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "pl" ≠ ofString "si" from by decide, hsi],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "pl" ≠ ofString "hdr" from by decide, hhdr],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    hpl_eq, by rw [hpl_eq]; exact hntx_le⟩

private theorem step_dec_ntx {F : Type} (s : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (h : PreNtx s)
    (hev : evalAt s (.load .one (.op .add [.var .local (ofString "pl"), .const 40#64])) = some v) :
    PreAllocBo (setVarHOLFinite (ofString "ntx") v s) := by
  obtain ⟨w_si, w_hdr, w_pl, S, Nd, hc, hsi, hhdr, hpl, hpl_eq, hntx_le⟩ := h
  obtain ⟨a, w_ntx, ha, rfl, hntx_eq, _, _, _⟩ := evalAt_load_one_word hc.arena.1 hev
  obtain ⟨w1, w2, hw1, hw2, rfl⟩ := evalAt_add2_words ha
  have hw1_eq : w1 = w_pl := by simpa [evalAt, evalHOLExact, hpl] using hw1.symm
  have hw2_eq : w2 = 40#64 := by simpa [evalAt, evalHOLExact] using hw2.symm
  subst w1; subst w2
  have hpl_in : (w_pl.toNat, 136) ∈ inputRegions s w_si.toNat w_hdr.toNat := by
    rw [hpl_eq]; simp [inputRegions]
  have hpl_hi : w_pl.toNat + 136 ≤ 2 ^ 64 :=
    (hc.regions _ hpl_in).2.2.1.2.trans (hc.arena.2.2.1.trans (by decide : heapLimit ≤ 2 ^ 64))
  have ha_eq : (w_pl + 40#64).toNat = w_pl.toNat + 40 := by
    rw [BitVec.toNat_add]
    exact Nat.mod_eq_of_lt (by change w_pl.toNat + 40 < 2 ^ 64; omega)
  rw [ha_eq] at hntx_eq
  set t := setVarHOLFinite (ofString "ntx") (.val (.word w_ntx)) s
  exact ⟨w_si, w_hdr, w_pl, w_ntx, S, Nd,
    (blockContext_with_locals s _ s.clock S Nd w_si.toNat w_hdr.toNat).2 hc,
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "ntx" ≠ ofString "si" from by decide, hsi],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "ntx" ≠ ofString "hdr" from by decide, hhdr],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, show ofString "ntx" ≠ ofString "pl" from by decide, hpl],
    by simp [t, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE],
    hpl_eq, hntx_eq, by rw [hntx_eq]; exact hntx_le⟩

private def progFromBoInit : ProgHOL 64 :=
  .seq (.call (some (none, none)) (ofString "bal_init") [])
    (.seq .skip
      (.seq (.call (some (none, none)) (ofString "process_unchecked_system_transaction")
              [.var .global (ofString "beacon_roots_address"),
               .load .one (.op .add [.var .local (ofString "si"), .const 24#64]),
               .const 32#64])
        (.dec (ofString "lasth") .one (.var .global (ofString "zero32"))
          (.seq
            (.ite (.cmp .lower (.const 0#64) (.var .global (ofString "block_hashes_n")))
              (.assign .local (ofString "lasth")
                (.op .add [.var .global (ofString "block_hashes"),
                  .panop .mul [.op .sub [.var .global (ofString "block_hashes_n"), .const 1#64], .const 32#64]]))
              .skip)
            (.seq (.call (some (none, none)) (ofString "process_unchecked_system_transaction")
                    [.var .global (ofString "history_storage_address"),
                     .var .local (ofString "lasth"),
                     .const 32#64])
              (.seq .skip
                (.seq (.call (some (none, none)) (ofString "state_fresh_tx") [])
                  (.seq (.call (some (none, none)) (ofString "track_ancestor_access") [.const 1#64])
                    (.dec (ofString "ptxs") .one (.load .one (.op .add [.var .local (ofString "pl"), .const 32#64]))
                      (.dec (ofString "i") .one (.const 0#64)
                        (.seq
                          (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) progTxLoopBody)
                          progExecBlockPostLoop)))))))))))

private def kFromBoInit : Nat :=
  (K.«bal_init» + 1) + (K.«process_unchecked_system_transaction» + 1) +
    (K.«process_unchecked_system_transaction» + 1) + (K.«state_fresh_tx» + 1) +
    (K.«track_ancestor_access» + 1) +
    (1944059872 + 1) * ((K.«decode_transaction» + 1) + (K.«process_transaction» + 1) + 1) +
    kExecBlockPostLoop

private theorem terminating_progFromBoInit
    (hal : TerminatingFunBoundedOn GuestInv (ofString "alloc") K.«alloc»)
    (hbi : TerminatingFunBoundedOn GuestInv (ofString "bal_init") K.«bal_init»)
    (hbal_rlp : TerminatingFunBoundedOn GuestInv (ofString "build_block_access_list_rlp") K.«build_block_access_list_rlp»)
    (hbmi : TerminatingFunBoundedOn BuildMptIndexedReady (ofString "build_mpt_indexed") K.«build_mpt_indexed»)
    (hcrh : TerminatingFunBoundedOn GuestInv (ofString "compute_requests_hash") K.«compute_requests_hash»)
    (hcsr : TerminatingFunBoundedOn WorldOK (ofString "compute_state_root") K.«compute_state_root»)
    (hdt : TerminatingFunBoundedOn GuestInv (ofString "decode_transaction") K.«decode_transaction»)
    (hkec : TerminatingFunBoundedOn GuestInv (ofString "keccak256") K.«keccak256»)
    (hlb : TerminatingFunBoundedOn GuestInv (ofString "logs_bloom") K.«logs_bloom»)
    (hmax : TerminatingFunBoundedOn GuestInv (ofString "max") K.«max»)
    (hmeq : TerminatingFunBoundedOn GuestInv (ofString "memeq") K.«memeq»)
    (hgpr : TerminatingFunBoundedOn ReqsFresh (ofString "process_general_purpose_requests") K.«process_general_purpose_requests»)
    (hpt : TerminatingFunBoundedOn TxReadyStrong (ofString "process_transaction") K.«process_transaction»)
    (hsys : TerminatingFunBoundedOn SysTxReadyStrong (ofString "process_unchecked_system_transaction") K.«process_unchecked_system_transaction»)
    (hpw : TerminatingFunBoundedOn WorldOK (ofString "process_withdrawals") K.«process_withdrawals»)
    (hsf : TerminatingFunBoundedOn GuestInv (ofString "state_fresh_tx") K.«state_fresh_tx»)
    (htaa : TerminatingFunBoundedOn GuestInv (ofString "track_ancestor_access") K.«track_ancestor_access»)
    (hvbal : TerminatingFunBoundedOn GuestInv (ofString "validate_block_access_list_gas_limit") K.«validate_block_access_list_gas_limit»)
    (wal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (RetAvoids (fun s _ w => [(w, (locN s "n" + 7) / 8 * 8)])) (ofString "alloc"))
    (rtal : Returns ArenaReady (fun s post p => FreshBlock s post p (locN s "n")) (ofString "alloc"))
    (wbi : WorldKeeps WorldOK (fun _ => [])
      ["bal_accounts", "bal_idx_accts", "bal_idx_stor", "bal_index", "bal_key_buf", "heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "bal_init"))
    (wbal : WorldKeeps WorldOK (fun _ => []) ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "build_block_access_list_rlp"))
    (wbmi : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
                 (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "build_mpt_indexed"))
    (wcsr : WorldKeeps WorldOK
      (fun s => [(locN s "out", 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "compute_state_root"))
    (wdt : WorldKeeps (fun s => WorldOK s ∧ DecodeTxReady s) (fun _ => [])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      (fun s r post S Nd => RetDecodedTx s r post S Nd ∧ RetBoSlicesKept s r post S Nd)
      (ofString "decode_transaction"))
    (wlb : WorldKeeps WorldOK
      (fun s => [(locN s "out", 256),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "logs_bloom"))
    (wgpr : WorldKeeps ReqsFresh
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
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 72, 80])]
      RetBoSlicesKept (ofString "process_general_purpose_requests"))
    (wpt : WorldKeeps TxReadyStrong
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
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []),
       ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd ∧ RetTransactionSlices s r post S Nd)
      (ofString "process_transaction"))
    (wsys : WorldKeeps WorldOK
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
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]), ("ts", []),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_unchecked_system_transaction"))
    (wpw : WorldKeeps WorldOK
      (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetBoSlicesKept (ofString "process_withdrawals"))
    (wsf : WorldKeeps WorldOK (fun _ => [])
      ["heap_ptr", "journal_n", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]), ("ts", []),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "state_fresh_tx"))
    (wtaa : WorldKeeps WorldOK (fun _ => [])
      []
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "track_ancestor_access"))
    (hro_vbal : ReadOnlyFn (ofString "validate_block_access_list_gas_limit")) :
    TerminatingProgBoundedOn BoInitialized progFromBoInit kFromBoInit := by
  unfold progFromBoInit
  have hpost : TerminatingProgBoundedOn (PostLoopBase true) progExecBlockPostLoop kExecBlockPostLoop :=
    terminating_progExecBlockPostLoop
      hal hbal_rlp hbmi hcrh hcsr hkec hlb hmax hmeq hgpr hpw hvbal
      wal rtal wbal wbmi wcsr wlb wgpr wpw hro_vbal
  have hloop : TerminatingProgBoundedOn TxLoopInv
      (.while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) progTxLoopBody)
      ((1944059872 + 1) * ((K.«decode_transaction» + 1) + (K.«process_transaction» + 1) + 1)) :=
    terminating_txLoop hdt hpt wdt wpt
  intro F s hc hP
  exact
    (TerminatingProgBoundedOn.seq_hoare
      (TerminatingProgBoundedOn.call_on hbi none []
        (callEntryOn_of_imp localsFree_guestInv boInitialized_guestInv _ _))
      (hoare_bal_init_boInit wbi)
      (seq_skip_on
        (TerminatingProgBoundedOn.seq_hoare
          (TerminatingProgBoundedOn.call_on hsys none _
            (callEntryOn_sysTxReadyStrong boInitialized_worldOK _))
          (hoare_systx_boInit _ wsys)
          (TerminatingProgBoundedOn.dec_onLocals localsOnly_boInitialized (ofString "lasth")
            (fun n hn => by
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
              rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
            .one (.var .global (ofString "zero32"))
            (TerminatingProgBoundedOn.seq_hoare
              (TerminatingProgBoundedOn.ite_on
                (straight_on
                  (.assign .local (ofString "lasth")
                    (.op .add [.var .global (ofString "block_hashes"),
                      .panop .mul [.op .sub [.var .global (ofString "block_hashes_n"), .const 1#64], .const 32#64]]))
                  rfl)
                (straight_on .skip rfl))
              hoare_ite_lasth_boInit
              (TerminatingProgBoundedOn.seq_hoare
                (TerminatingProgBoundedOn.call_on hsys none _
                  (callEntryOn_sysTxReadyStrong boInitialized_worldOK _))
                (hoare_systx_boInit _ wsys)
                (seq_skip_on
                  (TerminatingProgBoundedOn.seq_hoare
                    (TerminatingProgBoundedOn.call_on hsf none []
                      (callEntryOn_of_imp localsFree_guestInv boInitialized_guestInv _ _))
                    (hoare_state_fresh_tx_boInit wsf)
                    (TerminatingProgBoundedOn.seq_hoare
                      (TerminatingProgBoundedOn.call_on htaa none [.const 1#64]
                        (callEntryOn_of_imp localsFree_guestInv boInitialized_guestInv _ _))
                      (hoare_track_ancestor_access_boInit wtaa)
                      (dec_eval_on (ofString "ptxs") .one
                        (.load .one (.op .add [.var .local (ofString "pl"), .const 32#64]))
                        step_dec_ptxs
                        (dec_zero_on (ofString "i") step_dec_i_zero
                          (TerminatingProgBoundedOn.seq_hoare_trans
                            hloop (hoare_txLoop_exit wdt wpt) hpost)))))))))))
      s hc hP).weaken (by unfold kFromBoInit; omega)

private theorem boAfterStore72_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F)
    (h : BoAfterStore72 s) : GuestInv s := by
  obtain ⟨_, _, _, _, _, _, _, _, hc, _⟩ := h; exact hc.arena.1

theorem prove_gbody_execute_block_strong : GBody.«execute_block_strong» := by
  intro hal hbi hbal_rlp hbmi hcrh hcsr hdt hkec hlb hln hmax hmeq hmz hgpr hpt hsys hpw hsf htaa hvbal
    wal rtal wbi wbal wbmi wcsr wdt wlb wln rtln wmz wwmz zfmz wgpr wpt wsys wpw wsf wtaa hro_vbal
  refine ⟨_, _, _, lookup_execute_block, ?_⟩
  have hfromBoInit : TerminatingProgBoundedOn BoInitialized progFromBoInit kFromBoInit :=
    terminating_progFromBoInit
      hal hbi hbal_rlp hbmi hcrh hcsr hdt hkec hlb hmax hmeq hgpr hpt hsys hpw hsf htaa hvbal
      wal rtal wbi wbal wbmi wcsr wdt wlb wgpr wpt wsys wpw wsf wtaa hro_vbal
  simp only [sourceFunctionEntry, Guest.Software.guestFn_execute_block,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  change TerminatingProgBoundedOn BlockReadyExecStrong
    (.dec (ofString "pl") .one (.load .one (.op .add [.var .local (ofString "si"), .const 0#64]))
      (.dec (ofString "ntx") .one (.load .one (.op .add [.var .local (ofString "pl"), .const 40#64]))
        (.seq
          (.call (some (some (.global, ofString "bo"), none)) (ofString "alloc") [.const 88#64])
          (.seq
            (.call (some (none, none)) (ofString "memzero") [.var .global (ofString "bo"), .const 88#64])
            (.decCall (ofString "txs") .one (ofString "alloc")
              [.op .add [.panop .mul [.var .local (ofString "ntx"), .const 16#64], .const 16#64]]
              (.seq
                (.store (.op .add [.var .global (ofString "bo"), .const 24#64]) (.var .local (ofString "txs")))
                (.decCall (ofString "rcs") .one (ofString "alloc")
                  [.op .add [.panop .mul [.var .local (ofString "ntx"), .const 16#64], .const 16#64]]
                  (.seq
                    (.store (.op .add [.var .global (ofString "bo"), .const 32#64]) (.var .local (ofString "rcs")))
                    (.decCall (ofString "logs") .one (ofString "lst_new") [.const 8#64, .const 16#64]
                      (.seq
                        (.store (.op .add [.var .global (ofString "bo"), .const 40#64]) (.var .local (ofString "logs")))
                        (.decCall (ofString "reqs") .one (ofString "alloc")
                          [.panop .mul [.const 8#64, .const 16#64]]
                          (.seq
                            (.store (.op .add [.var .global (ofString "bo"), .const 56#64]) (.var .local (ofString "reqs")))
                            (.decCall (ofString "rls") .one (ofString "lst_new") [.const 8#64, .const 16#64]
                              (.seq
                                (.store (.op .add [.var .global (ofString "bo"), .const 72#64]) (.var .local (ofString "rls")))
                                (.seq
                                  (.store (.op .add [.var .global (ofString "bo"), .const 80#64]) (.var .local (ofString "ntx")))
                                  progFromBoInit)))))))))))))))
    K.«execute_block»
  intro F s hc hP
  exact
    (dec_eval_on (ofString "pl") .one
      (.load .one (.op .add [.var .local (ofString "si"), .const 0#64]))
      step_dec_pl
      (dec_eval_on (ofString "ntx") .one
        (.load .one (.op .add [.var .local (ofString "pl"), .const 40#64]))
        step_dec_ntx
        (TerminatingProgBoundedOn.seq_hoare_trans
          (TerminatingProgBoundedOn.call_on hal (some (.global, ofString "bo")) [.const 88#64]
            (callEntryOn_of_imp localsFree_guestInv preAllocBo_guestInv _ _))
          (hoare_call_global_bo_alloc wal rtal)
          (TerminatingProgBoundedOn.seq_hoare_trans
            (TerminatingProgBoundedOn.call_on hmz none [.var .global (ofString "bo"), .const 88#64]
              (callEntryOn_of_imp localsFree_guestInv preMemzeroBo_guestInv _ _))
            (hoare_call_memzero_bo wwmz zfmz)
            (TerminatingProgBoundedOn.decCall_on hal (ofString "txs") .one
              [.op .add [.panop .mul [.var .local (ofString "ntx"), .const 16#64], .const 16#64]]
              (callEntryOn_of_imp localsFree_guestInv boZeroState_guestInv _ _)
              (resumeOn_alloc_txs wal rtal)
              (TerminatingProgBoundedOn.seq_hoare_trans
                (straight_on (.store (.op .add [.var .global (ofString "bo"), .const 24#64]) (.var .local (ofString "txs"))) rfl)
                hoare_store_bo_24
                (TerminatingProgBoundedOn.decCall_on hal (ofString "rcs") .one
                  [.op .add [.panop .mul [.var .local (ofString "ntx"), .const 16#64], .const 16#64]]
                  (callEntryOn_of_imp localsFree_guestInv boAfterStore24_guestInv _ _)
                  (resumeOn_alloc_rcs wal rtal)
                  (TerminatingProgBoundedOn.seq_hoare_trans
                    (straight_on (.store (.op .add [.var .global (ofString "bo"), .const 32#64]) (.var .local (ofString "rcs"))) rfl)
                    hoare_store_bo_32
                    (TerminatingProgBoundedOn.decCall_on hln (ofString "logs") .one [.const 8#64, .const 16#64]
                      (callEntryOn_of_imp localsFree_guestInv boAfterStore32_guestInv _ _)
                      (resumeOn_lst_new_logs wln rtln)
                      (TerminatingProgBoundedOn.seq_hoare_trans
                        (straight_on (.store (.op .add [.var .global (ofString "bo"), .const 40#64]) (.var .local (ofString "logs"))) rfl)
                        hoare_store_bo_40
                        (TerminatingProgBoundedOn.decCall_on hal (ofString "reqs") .one
                          [.panop .mul [.const 8#64, .const 16#64]]
                          (callEntryOn_of_imp localsFree_guestInv boAfterStore40_guestInv _ _)
                          (resumeOn_alloc_reqs wal rtal)
                          (TerminatingProgBoundedOn.seq_hoare_trans
                            (straight_on (.store (.op .add [.var .global (ofString "bo"), .const 56#64]) (.var .local (ofString "reqs"))) rfl)
                            hoare_store_bo_56
                            (TerminatingProgBoundedOn.decCall_on hln (ofString "rls") .one [.const 8#64, .const 16#64]
                              (callEntryOn_of_imp localsFree_guestInv boAfterStore56_guestInv _ _)
                              (resumeOn_lst_new_rls wln rtln)
                              (TerminatingProgBoundedOn.seq_hoare_trans
                                (straight_on (.store (.op .add [.var .global (ofString "bo"), .const 72#64]) (.var .local (ofString "rls"))) rfl)
                                hoare_store_bo_72
                                (TerminatingProgBoundedOn.seq_hoare_trans
                                  (straight_on (.store (.op .add [.var .global (ofString "bo"), .const 80#64]) (.var .local (ofString "ntx"))) rfl)
                                  hoare_store_bo_80
                                  hfromBoInit))))))))))))))
      s hc hP).weaken (by unfold K.«execute_block» kFromBoInit kExecBlockPostLoop kExecBlockGuestTail; omega)

end ExecBlock

theorem gbody_execute_block_strong : GBody.«execute_block_strong» :=
  ExecBlock.prove_gbody_execute_block_strong

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
