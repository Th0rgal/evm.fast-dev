import InitECandidate.Solver.Wave8GuestInv.MemoryViews
import InitECandidate.Solver.Wave8GuestInv.Deliveries.M27.TeNewSupport

/-! Constructor return typing `rt_te_new` for micro-shard `m27` (`wave8/contracts-m27`),
frozen revision 9 (`8a79d9f28`, tag `wave8-spec-frozen-r9`).

Imports only the light split module `InitECandidate.Solver.Wave8GuestInv.MemoryViews` and
`campaign.contracts.m27.TeNewSupport`.
Restates `FunSpec`, `FreshBlock`, `RetWord`, and `Returns` verbatim from
`campaign/specs-proposed/GuestInv.lean` @ `8a79d9f28` so they delta-reduce definitionally (`rfl`)
to the spec statement in `Axioms.lean`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8Contracts.M27

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- Outcome specification of a function body from its callee-entry state
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def FunSpec_te (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      Q s (evaluateHOLFiniteState s body).1 (evaluateHOLFiniteState s body).2

/-- `[p, p + round8 n)` is heap allocated between `s` and `post`, `p` aligned, all words
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def FreshBlock {F : Type} (s post : PanSemStateFiniteExact 64 F) (p n : Nat) : Prop :=
  p % 8 = 0 ∧ Inside (p, (n + 7) / 8 * 8) (globN s "heap_ptr") (globN post "heap_ptr") ∧
    WordsOK post (p, (n + 7) / 8 * 8)

/-- A normal return is a word `w` with `Q s post w`
(verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def RetWord (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat →
    Prop) : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop :=
  fun s r post => ∀ v, r = some (.returned v) → ∃ w : BitVec 64, v = .val (.word w) ∧ Q s post w.toNat

/-- Constructor return contract (verbatim from `GuestInv.lean` @ `8a79d9f28`). -/
def Returns (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → PanSemStateFiniteExact 64 F → Nat → Prop)
    (fname : MlS) : Prop :=
  FunSpec_te P (RetWord (fun s post p => ArenaReady post ∧ AllocatorGrows s post ∧ Q s post p)) fname

private theorem addresses_iff (b : BitVec 64) (n : Nat) (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      ∃ i, i < n ∧ x = b + BitVec.ofNat 64 (8 * i) := by
  induction n generalizing b with
  | zero => simp [Flapjack.Compiler.Backend.StackRemove.addresses]
  | succ n ih =>
    simp only [Flapjack.Compiler.Backend.StackRemove.addresses,
      Flapjack.Compiler.Backend.StackRemove.bytesInWord]
    rw [ih]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by omega, by simp⟩
      · refine ⟨i + 1, by omega, ?_⟩
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega
    · rintro ⟨i, hi, rfl⟩
      rcases i with _ | i
      · left; simp
      · right
        refine ⟨i, by omega, ?_⟩
        rw [BitVec.add_assoc]
        congr 1
        apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]
        omega

private theorem ordinaryDomain_eq : ordinaryDomain =
    Flapjack.Compiler.Backend.StackRemove.addresses (BitVec.ofNat 64 2701131776) 3888119741 := by
  have h1 : (BitVec.ofNat 64 sourceBase) = BitVec.ofNat 64 2701131776 := rfl
  have h2 : (stackStart - sourceBase) / 8 - globalsWords = 3888119741 := by decide
  unfold ordinaryDomain
  rw [h1, h2]

private theorem addresses_iff_nat (b : BitVec 64) (n : Nat) (hb : b.toNat + 8 * n ≤ 2 ^ 64)
    (x : BitVec 64) :
    Flapjack.Compiler.Backend.StackRemove.addresses b n x ↔
      b.toNat ≤ x.toNat ∧ x.toNat < b.toNat + 8 * n ∧ (x.toNat - b.toNat) % 8 = 0 := by
  rw [addresses_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : (b + BitVec.ofNat 64 (8 * i)).toNat = b.toNat + 8 * i := by
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [this]
    omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨(x.toNat - b.toNat) / 8, by omega, ?_⟩
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega

private theorem ordinaryDomain_iff (x : BitVec 64) :
    ordinaryDomain x ↔ sourceBase ≤ x.toNat ∧ x.toNat < heapEnd ∧ x.toNat % 8 = 0 := by
  have hb : (BitVec.ofNat 64 2701131776).toNat = 2701131776 := rfl
  have hsb : sourceBase = 2701131776 := by decide
  have hhe : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  rw [ordinaryDomain_eq, addresses_iff_nat _ _ (by rw [hb]; norm_num), hb, hsb, hhe]
  omega

private theorem ordinaryDomain_of_nat (a : Nat) (hlo : sourceBase ≤ a) (hhi : a < heapEnd)
    (hal : a % 8 = 0) : ordinaryDomain (BitVec.ofNat 64 a) := by
  have hlt : a < 2 ^ 64 := by
    have : heapEnd < 2 ^ 64 := by decide
    omega
  have hbv : (BitVec.ofNat 64 a).toNat = a := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [ordinaryDomain_iff, hbv]
  exact ⟨hlo, hhi, hal⟩

private theorem wordsOK_of_guestInv {F : Type} (s : PanSemStateFiniteExact 64 F) (hG : GuestInv s)
    (p len : Nat) (hp : p % 8 = 0) (hlen : len % 8 = 0)
    (hlo : sourceBase ≤ p) (hhi : p + len ≤ heapEnd) :
    WordsOK s (p, len) := by
  refine ⟨hp, hlen, ?_⟩
  intro k hk
  rcases hmem : s.memory (BitVec.ofNat 64 (p + 8 * k)) with ⟨w⟩
  refine ⟨w, ?_, hmem⟩
  rw [hG.memaddrs]
  exact ordinaryDomain_of_nat (p + 8 * k) (by omega) (by omega) (by omega)

private theorem globWord_of_pos {F : Type} (s : PanSemStateFiniteExact 64 F) (name : String)
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

attribute [local irreducible] zeroBlock25 in
/-- `te_new` (AST line 32838): returns a fresh zeroed 200-byte transaction environment. -/
theorem rt_te_new :
    Returns ArenaReady (fun s post m => FreshBlock s post m 200 ∧
      ∀ k, k < 25 → memW post (m + 8 * k) = 0)
    (ofString "te_new") := by
  refine ⟨_, (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1, _, lookup_te_new, ?_⟩
  intro F s hcode hAR _ _ v hv
  obtain ⟨hGI, hA⟩ := hAR
  have hsb : sourceBase = 2701131776 := rfl
  have hhl : heapLimit = 2952790016 := rfl
  have hhe : heapEnd = 2701131776 + 8 * 3888119741 := by decide
  obtain ⟨hp, hhp, hhp_eq⟩ := globWord_of_pos s "heap_ptr" (by have := hA.1; omega)
  have hp_align : hp.toNat % 8 = 0 := by rw [hhp_eq]; exact hA.2.2.2.2.2.1
  have hp_le_lim : hp.toNat ≤ 2952790016 := by rw [hhp_eq, ← hhl]; exact hA.2.1
  rcases hpair : evaluateHOLFiniteState s
      (sourceFunctionEntry Guest.Software.guestFn_te_new).2.2.1 with ⟨res, post⟩
  rw [hpair] at hv
  dsimp only at hv
  subst hv
  have hdom_fn : ∀ (q : BitVec 64), q.toNat ≤ 2952790016 → q.toNat = hp.toNat + 200 →
      ∀ off : Nat, off < 200 → off % 8 = 0 → s.memaddrs (hp + BitVec.ofNat 64 off) := by
    intro q hq_le hq_nat off hoff hmod
    rw [hGI.memaddrs]
    have hlo_hp : sourceBase ≤ hp.toNat := by rw [hhp_eq]; exact hA.1
    have hadd_eq : hp + BitVec.ofNat 64 off = BitVec.ofNat 64 (hp.toNat + off) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [hadd_eq]
    exact ordinaryDomain_of_nat (hp.toNat + off) (by omega) (by omega) (by omega)
  obtain ⟨hv_eq, hq_nat, hq_le_num, hpost_mem, hpost_glob, hcode_p, hmem_p, hsh_p, hbase_p⟩ :=
    te_new_body_run s post hp v hcode hhp hp_align hp_le_lim hdom_fn hpair
  set q : BitVec 64 := (hp + (200#64 + 7#64)) &&& ((0 : BitVec 64) - 8)
  have hq_le : q.toNat ≤ heapLimit := by rw [hhl]; exact hq_le_num
  have hpost_gi : GuestInv post := guestInv_congr hcode_p hmem_p hsh_p hbase_p hGI
  have hg_hp : globN post "heap_ptr" = q.toNat := by
    unfold globN
    rw [hpost_glob]
    simp [HolFiniteMapExact.lookup_update, FUPDATE]
  have hg_fp : globN post "frame_mem_ptr" = globN s "frame_mem_ptr" := by
    unfold globN
    rw [hpost_glob]
    simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "frame_mem_ptr" by decide]
  have hg_sp : globN post "scratch_ptr" = globN s "scratch_ptr" := by
    unfold globN
    rw [hpost_glob]
    simp [HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "heap_ptr" ≠ ofString "scratch_ptr" by decide]
  have hAR_post : ArenaReady post := by
    refine ⟨hpost_gi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hg_hp, hq_nat, hhp_eq]; have := hA.1; omega
    · rw [hg_hp]; exact hq_le
    · rw [hg_fp]; exact hA.2.2.1
    · rw [hg_fp, hg_sp]; exact hA.2.2.2.1
    · rw [hg_sp]; exact hA.2.2.2.2.1
    · rw [hg_hp, hq_nat]; omega
    · rw [hg_fp]; exact hA.2.2.2.2.2.2.1
    · rw [hg_sp]; exact hA.2.2.2.2.2.2.2
  refine ⟨hp, hv_eq, hAR_post, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [hg_hp, hq_nat, hhp_eq]; omega
    · rw [hg_sp]
  · refine ⟨hp_align, ?_, ?_⟩
    · unfold Inside
      rw [hg_hp, hq_nat, ← hhp_eq]
      exact ⟨le_refl _, by omega⟩
    · rw [show (200 + 7) / 8 * 8 = 200 by decide]
      exact wordsOK_of_guestInv post hpost_gi hp.toNat 200 hp_align (by decide)
        (by rw [hhp_eq]; exact hA.1) (by omega)
  · intro k hk
    unfold memW
    have hbv_eq : BitVec.ofNat 64 (hp.toNat + 8 * k) = hp + BitVec.ofNat 64 (8 * k) := by
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [hbv_eq, hpost_mem, zeroBlock25_read s.memory hp k hk]
    rfl

end InitECandidate.Solver.Wave8Contracts.M27
